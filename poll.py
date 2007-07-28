# Copyright 2007 World Wide Workshop, Collabora Ltd.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA

import os
import pickle
import gtk
import hippo
import pango
import locale
import logging
from datetime import date
from gettext import gettext as _
import telepathy
import telepathy.client
from dbus import Interface
from dbus.service import method, signal
from dbus.gobject_service import ExportedGObject
from tubeconn import TubeConnection

try:
    from hashlib import sha1
except ImportError:
    # Python < 2.5
    from sha import new as sha1

from sugar.activity import activity
from sugar.graphics import color
from sugar.graphics.units import points_to_pixels as px
from sugar.presence import presenceservice
from abiword import Canvas as AbiCanvas
from i18n import LanguageComboBox

#logger = logging.getLogger('poll-activity')

SERVICE = "org.worldwideworkshop.PollBuilder"
IFACE = SERVICE
PATH = "/org/worldwideworkshop/PollBuilder"

# Theme definitions - colors
LIGHT_GREEN = '#66CC00'
DARK_GREEN = '#027F01'
PINK = '#FF0198'
YELLOW = '#FFFF00'
GRAY = '#ACACAC'
LIGHT_GRAY = '#E2E2E3'
RED = '#FF0000'

COLOR_FG_BUTTONS = (
    (gtk.STATE_NORMAL,"#CCFF99"),
    (gtk.STATE_ACTIVE,"#CCFF99"),
    (gtk.STATE_PRELIGHT,"#CCFF99"),
    (gtk.STATE_SELECTED,"#CCFF99"),
    (gtk.STATE_INSENSITIVE,"#CCFF99"),
    )
COLOR_BG_BUTTONS = (
    (gtk.STATE_NORMAL,"#027F01"),
    (gtk.STATE_ACTIVE,"#014D01"),
    (gtk.STATE_PRELIGHT,"#016D01"),
    (gtk.STATE_SELECTED,"#027F01"),
    (gtk.STATE_INSENSITIVE,"#027F01"),
    )
COLOR_BG_RADIOBUTTONS = (
    (gtk.STATE_NORMAL,LIGHT_GRAY),
    (gtk.STATE_ACTIVE,LIGHT_GRAY),
    (gtk.STATE_PRELIGHT,LIGHT_GRAY),
    (gtk.STATE_SELECTED,LIGHT_GRAY),
    (gtk.STATE_INSENSITIVE,LIGHT_GRAY),
    )
COLOR_FG_RADIOBUTTONS = (
    (gtk.STATE_NORMAL,DARK_GREEN),
    (gtk.STATE_ACTIVE,DARK_GREEN),
    (gtk.STATE_PRELIGHT,DARK_GREEN),
    (gtk.STATE_SELECTED,DARK_GREEN),
    (gtk.STATE_INSENSITIVE,DARK_GREEN),
    )

def theme_button(btn, w=-1, h=-1, highlight=False):
    """Apply colors to gtk Buttons
    
    btn is the button
    w and h are optional width and height for resizing the button
    highlight is a boolean to override the theme and apply a
        different color to show "you are here".

    returns the modified button.
    """
    for state, color in COLOR_BG_BUTTONS:
        if highlight:
            btn.modify_bg(state, gtk.gdk.color_parse("#CCFF99"))
        else:
            btn.modify_bg(state, gtk.gdk.color_parse(color))
    c = btn.get_child()
    if c is not None:
        for state, color in COLOR_FG_BUTTONS:
            if highlight:
                c.modify_fg(state, gtk.gdk.color_parse(DARK_GREEN))
            else:
                c.modify_fg(state, gtk.gdk.color_parse(color))
    else:
        for state, color in COLOR_FG_BUTTONS:
            btn.modify_fg(state, gtk.gdk.color_parse(color))
    if w>0 or h>0:
        btn.set_size_request(w, h)
    return btn

def theme_radiobutton(btn, size=12):
    """Apply colors and font to gtk RadioButtons
    
    btn -- gtk RadioButton
    size -- integer for font size

    returns the modified button.
    """
    if type(size) != type(1):
        size = 12
    for state, color in COLOR_BG_RADIOBUTTONS:
        btn.modify_bg(state, gtk.gdk.color_parse(color))
    c = btn.get_child()
    if c is not None:
        for state, color in COLOR_FG_RADIOBUTTONS:
            c.modify_fg(state, gtk.gdk.color_parse(color))
        c.modify_font(pango.FontDescription('Sans %d' % size))
    else:
        for state, color in COLOR_FG_RADIOBUTTONS:
            btn.modify_fg(state, gtk.gdk.color_parse(color))
        btn.modify_font(pango.FontDescription('Sans %d' % size))
    return btn


class PollBuilder(activity.Activity):
    """Sugar activity for polls

    Poll implements a simple tool that allows children to express
    their opinions on a given topic by selecting one of five
    answer choices and submitting a vote. The results are tallied
    by total number of votes and percentage of total votes cast.
    
    A future version of this activity will be networked over the
    OLPC mesh to allow sharing of the poll.
    
    """
    def __init__(self, handle):
        activity.Activity.__init__(self, handle)
        # XXX Make self.poll_ stuff into a dict for easier loading and saving
        # or even a class of its own

        self._logger = logging.getLogger('poll-activity')
        self._logger.debug('Starting Poll activity')

        self._basepath = activity.get_bundle_path()
        os.chdir(self._basepath)  # required for i18n.py to work
        self.journal_path = os.path.join(os.path.expanduser("~"), "Journal", "poll-builder")
        if (not os.path.exists(self.journal_path)):
            os.makedirs(self.journal_path)
        self.journal_index = os.path.join(self.journal_path, 'pollindex.txt')

        self._journal_index_load()

        # setup poll with default if journal index empty
        if self._polls_index == {}:
            self._make_default_poll()
            self._write_to_journal(update_index=True)
        else:
            self._make_blank_poll()
        self._has_voted = False
        self._preview = False
        self._current_view = None  # so we can switch back

        self.set_title(_('Poll Builder'))

        toolbox = activity.ActivityToolbox(self)
        self.set_toolbox(toolbox)
        toolbox.show()

        # Show poll screen
        # Setup screen
        self._canvas = hippo.Canvas()
        self._canvas.set_root(self._select_canvas())
        self.set_canvas(self._canvas)
        self.show_all()

        self.poll_session = None  # PollSession

        # get the Presence Service
        self.pservice = presenceservice.get_instance()
        name, path = self.pservice.get_preferred_connection()
        self.tp_conn_name = name
        self.tp_conn_path = path
        self.conn = telepathy.client.Connection(name, path)
        self.initiating = None
        
        self.connect('shared', self._shared_cb)

        # Buddy object for you
        owner = self.pservice.get_owner()
        self.owner = owner

        if self._shared_activity:
            # we are joining the activity
            self.connect('joined', self._joined_cb)
            self._shared_activity.connect('buddy-joined',
                                          self._buddy_joined_cb)
            self._shared_activity.connect('buddy-left',
                                          self._buddy_left_cb)
            if self.get_shared():
                # we've already joined
                self._joined_cb()

    def _poll_canvas(self):
        """Show the poll canvas where children vote on an existing poll."""
        self._current_view = 'poll'
        canvasbox = self._canvas_root()

        # pollbuilderbox is centered within canvasbox
        pollbuilderbox = self._canvas_pollbuilder_box()
        canvasbox.append(pollbuilderbox)

        pollbuilderbox.append(self._canvas_topbox())

        mainbox = self._canvas_mainbox()
        pollbuilderbox.append(mainbox)

        if not self._preview:
            mainbox.append(self._text_mainbox(_('VOTE!')))
        else:
            mainbox.append(self._text_mainbox(_('Poll Preview')))

        poll_details_box = hippo.CanvasBox(spacing=8,
            background_color=color.WHITE.get_int(),
            border=4,
            border_color=color.HTMLColor(PINK).get_int(),
            padding=20,
            xalign=hippo.ALIGNMENT_START,
            orientation=hippo.ORIENTATION_VERTICAL)
        mainbox.append(poll_details_box)
        self.poll_details_box = poll_details_box

        self.current_vote = None
        self.draw_poll_details_box()

        button_box = self._canvas_buttonbox()
        mainbox.append(button_box, hippo.PACK_END)

        return canvasbox

    def _select_canvas(self):
        """Show the select canvas where children choose an existing poll."""
        self._current_view = 'select'
        canvasbox = self._canvas_root()

        # pollbuilderbox is centered within canvasbox
        pollbuilderbox = self._canvas_pollbuilder_box()
        canvasbox.append(pollbuilderbox)

        pollbuilderbox.append(self._canvas_topbox())

        mainbox = self._canvas_mainbox()
        pollbuilderbox.append(mainbox)

        mainbox.append(self._text_mainbox(_('Choose a Poll')))

        poll_details_box = hippo.CanvasBox(spacing=8,
            background_color=color.WHITE.get_int(),
            border=4,
            border_color=color.HTMLColor(PINK).get_int(),
            padding=20,
            xalign=hippo.ALIGNMENT_START,
            orientation=hippo.ORIENTATION_VERTICAL)
        mainbox.append(poll_details_box)

        # add scroll window XXX add to canvas how?
        scrolledwindow = gtk.ScrolledWindow()
        scrolledwindow.set_policy(
            hscrollbar_policy=gtk.POLICY_NEVER,
            vscrollbar_policy=gtk.POLICY_AUTOMATIC)

        poll_selector_box = hippo.CanvasBox(
            orientation=hippo.ORIENTATION_VERTICAL)
        poll_details_box.append(poll_selector_box)  # XXX scrolledwindow?

        row_number = 0
        for title in self._polls_index.keys():
            poll = self._polls_index[title]
            if row_number % 2:
                row_bgcolor=color.WHITE.get_int()
            else:
                row_bgcolor=color.DESKTOP_BACKGROUND.get_int()
            row_number += 1
            poll_row = hippo.CanvasBox(
                padding_top=4, padding_bottom=4,
                background_color=row_bgcolor,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            poll_selector_box.append(poll_row)

            sized_box = hippo.CanvasBox(
                box_width=600,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            poll_row.append(sized_box)
            title = hippo.CanvasText(
                text=title+' ('+poll['author']+')',
                xalign=hippo.ALIGNMENT_START,
                color=color.HTMLColor(DARK_GREEN).get_int(),
                font_desc = pango.FontDescription('Sans 10'))
            sized_box.append(title)

            sized_box = hippo.CanvasBox(
                box_width=180,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            poll_row.append(sized_box)
            if poll['active']:
                button = gtk.Button(_('VOTE'))
            else:
                button = gtk.Button(_('SEE RESULTS'))
            button.connect('clicked', self._select_poll_button_cb,
                           poll['sha'])
            sized_box.append(hippo.CanvasWidget(widget=theme_button(button)))

            sized_box = hippo.CanvasBox(
                box_width=150,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            poll_row.append(sized_box)
            if poll['author'] == self._pservice.get_owner().props.nick:
                button = gtk.Button(_('DELETE'))
                button.connect('clicked', self._delete_poll_button_cb,
                               poll['sha'])
                sized_box.append(hippo.CanvasWidget(widget=theme_button(button)))
            poll_row.append(hippo.CanvasText(
                text=self.poll_createdate.strftime('%d/%m/%y'),
                color=color.HTMLColor(DARK_GREEN).get_int()))

        button_box = self._canvas_buttonbox(button_to_highlight=2)
        mainbox.append(button_box, hippo.PACK_END)

        return canvasbox

    def _lessonplan_canvas(self):
        """Show the select canvas where children choose an existing poll."""
        previous_view = self._current_view
        self._current_view = 'lessonplan'
        canvasbox = self._canvas_root()

        # pollbuilderbox is centered within canvasbox
        pollbuilderbox = self._canvas_pollbuilder_box()
        canvasbox.append(pollbuilderbox)

        pollbuilderbox.append(self._canvas_topbox(lesson_return=previous_view))

        mainbox = self._canvas_mainbox()
        pollbuilderbox.append(mainbox)

        mainbox.append(self._text_mainbox(_('Lesson Plans')))

        poll_details_box = hippo.CanvasBox(spacing=8,
            background_color=color.WHITE.get_int(),
            border=4,
            border_color=color.HTMLColor(PINK).get_int(),
            padding=20,
            xalign=hippo.ALIGNMENT_START,
            orientation=hippo.ORIENTATION_VERTICAL)
        mainbox.append(poll_details_box)

        lessonplan = LessonPlanWidget(self._basepath)
        lessonplan.set_size_request(1050, 500)
        poll_details_box.append(hippo.CanvasWidget(widget=lessonplan),
                                hippo.PACK_EXPAND)

        button_box = self._canvas_buttonbox()
        mainbox.append(button_box, hippo.PACK_END)

        return canvasbox

    def _select_poll_button_cb(self, button, sha=None):
        """A VOTE or SEE RESULTS button was clicked."""
        if not sha:
            self._logger.debug('Strange, which button was clicked?')
            return
        self._resume_from_journal(sha)
        self._has_voted = False
        self._canvas.set_root(self._poll_canvas())
        self.show_all()

    def _delete_poll_button_cb(self, button, sha=None):
        """A DELETE button was clicked."""
        if not sha:
            self._logger.debug('Strange, which button was clicked?')
            return
        self._journal_index_del(sha)
        self._canvas.set_root(self._select_canvas())
        self.show_all()
        
    def draw_poll_details_box(self):
        """(Re)draw the poll details box
        
        self.poll_details_box should be already defined on the canvas.
        """
        poll_details_box = self.poll_details_box
        poll_details_box.remove_all()

        votes_total = self.get_votes_total()

        text_size = self._size_heading_text(self.poll_title)
        title = hippo.CanvasText(
            text=self.poll_title,
            xalign=hippo.ALIGNMENT_START,
            color=color.HTMLColor(DARK_GREEN).get_int(),
            font_desc = pango.FontDescription('Sans %d' % text_size))
        poll_details_box.append(title)
        text_size = self._size_heading_text(self.poll_question)
        question = hippo.CanvasText(
            text=self.poll_question,
            xalign=hippo.ALIGNMENT_START,
            color=color.HTMLColor(DARK_GREEN).get_int(),
            font_desc = pango.FontDescription('Sans %d' % text_size))
        poll_details_box.append(question)

        button = None  # required for radio button group
        button = gtk.RadioButton()
        for choice in range(self.poll_number_of_options):
            self._logger.debug(self.poll_options[choice])
            answer_row = hippo.CanvasBox(spacing=8,
                orientation=hippo.ORIENTATION_HORIZONTAL)

            sized_box = hippo.CanvasBox(
                box_width=400,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            answer_row.append(sized_box)
            if self.poll_active:
                button = gtk.RadioButton(button, ' '+self.poll_options[choice])
                button.set_size_request(400, -1)
                button.connect('toggled', self.vote_choice_radio_button, choice)
                sized_box.append(hippo.CanvasWidget(
                    widget=theme_radiobutton(
                        button,
                        size=self._size_answer_text(choice))))
            else:
                sized_box.append(hippo.CanvasText(
                    text=self.poll_options[choice],
                    color=color.HTMLColor(DARK_GREEN).get_int(),
                    font_desc = pango.FontDescription('Sans %d' %
                        self._size_answer_text(choice))))

            # show results if the user has just voted,
            # unless the poll is closed - then show it straight away
            if votes_total > 0 and ((self.poll_active and self._has_voted) or
                                    not self.poll_active):
                # show results
                self._logger.debug(str(self.poll_data[choice] * 1.0 / votes_total))
                result_box = hippo.CanvasBox(
                    orientation=hippo.ORIENTATION_VERTICAL,
                    box_width=100)
                answer_row.append(result_box)
                result_box.append(hippo.CanvasText(
                    #text=str(self.poll_data[choice]),
                    text=justify(self.poll_data, choice),
                    xalign=hippo.ALIGNMENT_END,
                    color=color.HTMLColor(DARK_GREEN).get_int(),
                    font_desc = pango.FontDescription('Sans 12')))
                # int(self.poll_data[choice] * 1.0 / votes_total * 20) * '*',
                # APPEND BARGRAPH TO result_box
                graphbox = hippo.CanvasBox(
                    orientation=hippo.ORIENTATION_HORIZONTAL,
                    background_color=color.HTMLColor(PINK).get_int(),
                    box_width=int(self.poll_data[choice] * 1.0 / votes_total * 20) * 20)
                answer_row.append(graphbox)
                answer_row.append(hippo.CanvasText(
                    text=str(self.poll_data[choice] * 100 / votes_total)+'%',
                    color=color.HTMLColor(DARK_GREEN).get_int(),
                    font_desc=pango.FontDescription('Sans 10')))

            poll_details_box.append(answer_row)

        if (self.poll_active and self._has_voted) or\
            not self.poll_active:
            # Line above total
            line_box = hippo.CanvasBox(
                spacing=8,
                box_height=4,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            spacer = hippo.CanvasBox(
                box_width=430, orientation=hippo.ORIENTATION_HORIZONTAL)
            line_box.append(spacer)
            line = hippo.CanvasBox(
                background_color=color.HTMLColor(DARK_GREEN).get_int(),
                box_width=600,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            line_box.append(line)
            poll_details_box.append(line_box)

            # total votes
            totals_box = hippo.CanvasBox(
                spacing=8,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            poll_details_box.append(totals_box)
            spacer = hippo.CanvasBox(
                box_width=400, orientation=hippo.ORIENTATION_HORIZONTAL)
            totals_box.append(spacer)
            spacer = hippo.CanvasBox(
                box_width=100, orientation=hippo.ORIENTATION_VERTICAL)
            spacer.append(hippo.CanvasText(
                text=str(votes_total),
                xalign=hippo.ALIGNMENT_END,
                color=color.HTMLColor(DARK_GREEN).get_int(),
                font_desc = pango.FontDescription('Sans 12')))
            totals_box.append(spacer)
            totals_box.append(hippo.CanvasText(
                text=' '+_('votes'),
                xalign=hippo.ALIGNMENT_START,
                color=color.HTMLColor(DARK_GREEN).get_int(),
                font_desc = pango.FontDescription('Sans 12')))
            if votes_total < self.poll_maxvoters:
                totals_box.append(hippo.CanvasText(
                    text=' ('+str(self.poll_maxvoters-votes_total)+
                         ' votes left to collect)',
                    color=color.HTMLColor(DARK_GREEN).get_int(),
                    font_desc = pango.FontDescription('Sans 12')))

        # Button area
        if self.poll_active and not self._preview:
            button_box = hippo.CanvasBox(spacing=8,
                padding = 8,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            button = gtk.Button(_("Vote"))
            button.connect('clicked', self.button_vote_clicked)
            button_box.append(hippo.CanvasWidget(widget=theme_button(button)))
            poll_details_box.append(button_box)
        elif self._preview:
            button_box = hippo.CanvasBox(spacing=8,
                padding = 8,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            button = gtk.Button(_("Edit Poll"))
            button.connect('clicked', self.button_edit_clicked)
            button_box.append(hippo.CanvasWidget(widget=theme_button(button)))
            button = gtk.Button(_("Save Poll"))
            button.connect('clicked', self._button_save_cb)
            button_box.append(hippo.CanvasWidget(widget=theme_button(button)))
            poll_details_box.append(button_box)

    def vote_choice_radio_button(self, widget, data=None):
        """Track which radio button has been selected

        This is connected to the vote choice radio buttons.
        data contains the choice (0 - 4) selected.
        """
        self.current_vote = data

    def button_vote_clicked(self, button):
        """Register a vote

        Take the selected option from self.current_vote
        and increment the poll_data.
        """
        if self.current_vote is not None:
            if self.get_votes_total() >= self.poll_maxvoters:
                self._logger.debug(
                    'Hit the max voters, ignoring this vote.')
                return
            self._logger.debug('Voted '+str(self.current_vote))
            self._has_voted = True
            self.poll_data[self.current_vote] += 1
            if self.get_votes_total() >= self.poll_maxvoters:
                self.poll_active = False  # close poll
            self._logger.debug('Results: '+str(self.poll_data))
            self.draw_poll_details_box()
            # Update index when writing as poll may have closed:
            self._write_to_journal(update_index=True)

    def button_select_clicked(self, button):
        """Show Choose a Poll canvas"""
        self._canvas.set_root(self._select_canvas())
        self.show_all()

    def button_new_clicked(self, button):
        """Show Build a Poll canvas.

        Make sure current poll is saved.
        """
        if self.poll_title:
            self._write_to_journal(update_index=True)
        # Reset vote data to 0
        self._make_blank_poll()
        owner = self._pservice.get_owner()
        self.poll_author = owner.props.nick
        self.poll_active = False
        self._canvas.set_root(self._build_canvas())
        self.show_all()

    def button_edit_clicked(self, button):
        """Go back from preview to edit"""
        self._canvas.set_root(self._build_canvas())
        self.show_all()

    def _build_canvas(self, editing=False, highlight=[]):
        """Show the canvas to set up a new poll.
        
        editing is False to start a new poll, or
        True to edit the current poll

        highlight is a list of strings denoting items failing validation.
        """
        self._current_view = 'build'
        canvasbox = self._canvas_root()

        # pollbuilderbox is centered within canvasbox
        pollbuilderbox = self._canvas_pollbuilder_box()
        canvasbox.append(pollbuilderbox)

        pollbuilderbox.append(self._canvas_topbox())

        mainbox = self._canvas_mainbox()
        pollbuilderbox.append(mainbox)

        mainbox.append(self._text_mainbox(_('Build a Poll')))

        poll_details_box = hippo.CanvasBox(spacing=8,
            background_color=color.WHITE.get_int(),
            border=4,
            border_color=color.HTMLColor(PINK).get_int(),
            padding=20,
            xalign=hippo.ALIGNMENT_START,
            orientation=hippo.ORIENTATION_VERTICAL)
        mainbox.append(poll_details_box)

        buildbox = hippo.CanvasBox(spacing=8,
            #xalign=hippo.ALIGNMENT_CENTER,
            orientation=hippo.ORIENTATION_VERTICAL)
        poll_details_box.append(buildbox, hippo.PACK_EXPAND)
        
        hbox = hippo.CanvasBox(spacing=8,
            orientation=hippo.ORIENTATION_HORIZONTAL)
        hbox.append(self._text_mainbox(_('Poll Title:'),
                                       warn='title' in highlight))
        entrybox = gtk.Entry()
        entrybox.set_size_request(800, -1)
        entrybox.set_text(self.poll_title)
        entrybox.connect('changed', self._entry_activate_cb, 'title')
        hbox.append(hippo.CanvasWidget(widget=entrybox), hippo.PACK_EXPAND)
        buildbox.append(hbox, hippo.PACK_EXPAND)

        hbox = hippo.CanvasBox(spacing=8,
            orientation=hippo.ORIENTATION_HORIZONTAL)
        hbox.append(self._text_mainbox(_('Question:'),
                                       warn='question' in highlight))
        entrybox = gtk.Entry()
        entrybox.set_text(self.poll_question)
        entrybox.connect('changed', self._entry_activate_cb, 'question')
        hbox.append(hippo.CanvasWidget(widget=entrybox), hippo.PACK_EXPAND)
        buildbox.append(hbox, hippo.PACK_EXPAND)

        hbox = hippo.CanvasBox(spacing=8,
            orientation=hippo.ORIENTATION_HORIZONTAL)
        hbox.append(self._text_mainbox(_('Number of votes to collect:'),
                                       warn='maxvoters' in highlight))
        entrybox = gtk.Entry()
        entrybox.set_text(str(self.poll_maxvoters))
        entrybox.connect('changed', self._entry_activate_cb, 'maxvoters')
        hbox.append(hippo.CanvasWidget(widget=entrybox))
        buildbox.append(hbox)

        for choice in self.poll_options.keys():
            hbox = hippo.CanvasBox(spacing=8,
                orientation=hippo.ORIENTATION_HORIZONTAL)
            hbox.append(self._text_mainbox(_('Answer') + ' ' + str(choice+1) +
                                           ':',
                                           warn=str(choice) in highlight))
            entrybox = gtk.Entry()
            entrybox.set_text(self.poll_options[choice])
            entrybox.connect('changed', self._entry_activate_cb, str(choice))
            hbox.append(hippo.CanvasWidget(widget=entrybox), hippo.PACK_EXPAND)
            buildbox.append(hbox, hippo.PACK_EXPAND)

        # PREVIEW & SAVE buttons
        hbox = hippo.CanvasBox(spacing=8,
            orientation=hippo.ORIENTATION_HORIZONTAL)
        button = gtk.Button(_("Step 1: Preview"))
        button.connect('clicked', self._button_preview_cb)
        hbox.append(hippo.CanvasWidget(widget=theme_button(button)))
        button = gtk.Button(_("Step 2: Save"))
        button.connect('clicked', self._button_save_cb)
        hbox.append(hippo.CanvasWidget(widget=theme_button(button)))
        buildbox.append(hbox)
        
        button_box = self._canvas_buttonbox(button_to_highlight=1)
        mainbox.append(button_box, hippo.PACK_END)

        return canvasbox

    def _button_preview_cb(self, button, data=None):
        """Preview button clicked."""
        # Validate data
        failed_items = self._validate()
        if failed_items:
            self._canvas.set_root(self._build_canvas(highlight=failed_items))
            self.show_all()
            return
        # Data OK
        self.poll_active = True  # Show radio buttons
        self._preview = True
        self._canvas.set_root(self._poll_canvas())
        self.show_all()

    def _button_save_cb(self, button, data=None):
        """Save button clicked."""
        # Validate data
        failed_items = self._validate()
        if failed_items:
            self._canvas.set_root(self._build_canvas(highlight=failed_items))
            self.show_all()
            return
        # Data OK
        self._preview = False
        self.poll_active = True
        self._write_to_journal(update_index=True)
        self._canvas.set_root(self._poll_canvas())
        self.show_all()

    def _entry_activate_cb(self, entrycontrol, data=None):
        text = entrycontrol.props.text
        if data:
            if text:
                if data=='title':
                    self.poll_title = text
                elif data=='question':
                    self.poll_question = text
                elif data=='maxvoters':
                    try:
                        self.poll_maxvoters = int(text)
                    except ValueError:
                        self.poll_maxvoters = 0  # invalid, will be trapped
                else:
                    self.poll_options[int(data)] = text

    def _make_blank_poll(self):
        """Initialize the poll state."""
        self.poll_title = self.poll_author = ''
        self.poll_active = False
        self.poll_createdate = date.today()
        self.poll_maxvoters = 20
        self.poll_question = ''
        self.poll_number_of_options = 5
        self.poll_options = {0: '', 1: '', 2: '', 3: '', 4: ''}
        self.poll_data = {0: 0, 1:0, 2:0, 3:0, 4:0}
        self.current_vote = None

    def _make_default_poll(self):
        """A hardcoded poll for first time launch."""
        self.poll_title = _('Favorite Color')
        self.poll_createdate = date.today()
        owner = self._pservice.get_owner()
        self.poll_author = owner.props.nick
        self.poll_active = True
        self.poll_maxvoters = 20
        self.poll_question = _('What is your favorite color?')
        self.poll_number_of_options = 5
        self.poll_options = {
            0: _('Green'),
            1: _('Red'),
            2: _('Blue'),
            3: _('Orange'),
            4: _('None of the above'),
        }
        self.poll_data = {0: 0, 1:0, 2:0, 3:0, 4:0}
        self.current_vote = None
        # XXX The above must be extended to cater for only one vote per XO, tracking
        # an anonymous but unique identifier per XO and the vote cast
        self._journal_index_add()

    def _validate(self):
        failed_items = []
        if self.poll_title == '':
            failed_items.append('title')
        if self.poll_question == '':
            failed_items.append('question')
        if self.poll_maxvoters == 0:
            failed_items.append('maxvoters')
        if self.poll_options[0] == '':
            failed_items.append('0')
        if self.poll_options[1] == '':
            failed_items.append('1')
        if self.poll_options[3] != '' and self.poll_options[2] == '':
            failed_items.append('2')
        if self.poll_options[4] != '' and self.poll_options[3] == '':
            failed_items.append('3')
        if self.poll_options[2] == '':
            self.poll_number_of_options = 2
        elif self.poll_options[3] == '':
            self.poll_number_of_options = 3
        elif self.poll_options[4] == '':
            self.poll_number_of_options = 4
        else:
            self.poll_number_of_options = 5
        return failed_items
            
    def _write_to_journal(self, update_index=False):
        """Write current poll to journal.
        
        Pass update_index=True if you need to make sure
        this poll is in the journal index file. For example,
        when creating a new poll.
        """
        sha = self._get_sha()
        self.filename = os.path.join(self.journal_path, sha)
        f = open(self.filename, 'w')
        pickle.dump(self.poll_title, f)
        pickle.dump(self.poll_author, f)
        pickle.dump(self.poll_active, f)
        pickle.dump(self.poll_createdate, f)
        pickle.dump(self.poll_maxvoters, f)
        pickle.dump(self.poll_question, f)
        pickle.dump(self.poll_number_of_options, f)
        pickle.dump(self.poll_options, f)
        pickle.dump(self.poll_data, f)
        f.close()
        if update_index:
            self._journal_index_add()

    def _journal_index_add(self):
        """Write the current poll to the journal index."""
        self._journal_index_load()
        # insert self
        self._polls_index[self.poll_title] = {
            'author': self.poll_author,
            'active': self.poll_active,
            'createdate': self.poll_createdate,
            'sha': self._get_sha(),
        }
        # write index
        self._journal_index_write()

    def _journal_index_del(self, sha):
        """Delete a poll from the journal index."""
        self._journal_index_load()
        for poll in self._polls_index.keys():
            if self._polls_index[poll]['sha'] == sha:
                del self._polls_index[poll]
                self._journal_index_write()
                return

    def _get_sha(self):
        """Return a sha1 hash of something about this poll.
        
        Currently we sha1 the poll title and author.
        This is used for the filename of the saved poll.
        It will probably be used for the mesh networking too.
        """
        sha = sha1(self.poll_title + self.poll_author).hexdigest()
        return sha
    
    def _journal_index_load(self):
        """Load the journal index of saved polls."""
        self._polls_index = {}
        try:
            lines = open(self.journal_index).readlines()
        except IOError:  # File does not exist
            lines = []
        for line in lines:
            try:
                title, author, active, createdate, sha =\
                    line.strip().split('\t')
            except ValueError:
                # incompatible file format change
                self._logger.debug('Loading journal index file failed, resetting')
                continue
            self._polls_index[title] = {
                'author': author, 'active': int(active),
                'createdate': date.fromordinal(int(createdate)), 'sha': sha}

    def _journal_index_write(self):
        """Write the journal file."""
        # XXX Need to validate self._polls_index!
        f = open(self.journal_index, 'w')
        for title in self._polls_index.keys():
            f.write('%s\t%s\t%d\t%d\t%s\n' % 
                    (title,
                     self._polls_index[title]['author'],
                     self._polls_index[title]['active'],
                     self._polls_index[title]['createdate'].toordinal(),
                     self._polls_index[title]['sha']))
        f.close()

    def _resume_from_journal(self, sha):
        """Load from journal based on the sha

        The sha comes from the index file.
        """
        self.sha = sha
        self.filename = os.path.join(self.journal_path, self.sha)
        f = open(self.filename)
        self.poll_title = pickle.load(f)
        self.poll_author = pickle.load(f)
        self.poll_active = pickle.load(f)
        self.poll_createdate = pickle.load(f)
        self.poll_maxvoters = pickle.load(f)
        self.poll_question = pickle.load(f)
        self.poll_number_of_options = pickle.load(f)
        self.poll_options = pickle.load(f)
        self.poll_data = pickle.load(f)
        f.close()

    def get_votes_total(self):
        """Return the total votes cast."""
        total = 0
        for choice in self.poll_options.keys():
            total += self.poll_data[choice]
        return total

    def _canvas_language_select_box(self):
        """CanvasBox definition for lang select box.
        
        Called from _poll_canvas, _select_canvas, _build_canvas
        """
        languageselectbox = hippo.CanvasBox(
            background_color=color.HTMLColor(LIGHT_GREEN).get_int(),
            border_top=4, border_left=4,
            border_color=color.HTMLColor(YELLOW).get_int(),
            padding_top=12, padding_bottom=12,
            padding_left=100, padding_right=100,
            orientation=hippo.ORIENTATION_VERTICAL)
        button = LanguageComboBox()
        button.install()
        languageselectbox.append(hippo.CanvasWidget(widget=theme_button(button)))
        return languageselectbox

    def _canvas_pollbuilder_box(self):
        """CanvasBox definition for pollbuilderbox.
        
        Called from _poll_canvas, _select_canvas, _build_canvas
        """
        pollbuilderbox = hippo.CanvasBox(
            border=4,
            border_color=color.HTMLColor(GRAY).get_int(),
            orientation=hippo.ORIENTATION_VERTICAL)
        return pollbuilderbox

    def _canvas_root(self):
        """CanvasBox definition for main canvas.
        
        Called from _poll_canvas, _select_canvas, _build_canvas
        """
        canvasbox = hippo.CanvasBox(
            background_color=color.DESKTOP_BACKGROUND.get_int(),
            #padding = 100,
            orientation=hippo.ORIENTATION_VERTICAL)
        return canvasbox

    def _canvas_topbox(self, lesson_return=None):
        """Render topbox.

        lesson_return is the view we want to return to from
        lesson plan if the lesson plan button is clicked.
        """
        topbox = hippo.CanvasBox(
            background_color=color.HTMLColor(LIGHT_GREEN).get_int(),
            orientation=hippo.ORIENTATION_HORIZONTAL)
        topbox.append(hippo.CanvasWidget(widget=self._logo()))
        languageselectbox = self._canvas_language_select_box()
        topbox.append(languageselectbox, hippo.PACK_EXPAND)
        lessonplanbox = self._canvas_lessonplanbox(lesson_return)
        topbox.append(lessonplanbox, hippo.PACK_EXPAND)
        return topbox

    def _logo(self):
        logoimage = gtk.Image()
        logoimage.set_from_file(os.path.join(
            self._basepath,
            'GameLogoCharacter.png'))
        return logoimage

    def _canvas_lessonplanbox(self, lesson_return=None):
        """Render the lessonplanbox.

        disconnect_lp True does not connect the button.
        """
        lessonplanbox = hippo.CanvasBox(
            background_color=color.HTMLColor(LIGHT_GREEN).get_int(),
            border_top=4, border_left=4, border_right=4,
            border_color=color.HTMLColor(YELLOW).get_int(),
            padding_top=12, padding_bottom=12,
            padding_left=30, padding_right=30,
            orientation=hippo.ORIENTATION_VERTICAL)
        if lesson_return:
            highlight = True
            button = gtk.Button(_("Close Lessons"))
        else:
            highlight = False
            button = gtk.Button(_("Lesson Plans"))
        if lesson_return:
            button.connect('clicked', self._button_closelessonplan_cb, lesson_return)
        else:
            button.connect('clicked', self._button_lessonplan_cb)
        lessonplanbox.append(hippo.CanvasWidget(widget=theme_button(
            button, highlight=highlight)))
        return lessonplanbox

    def _button_lessonplan_cb(self, button):
        """Lesson Plan button clicked."""
        self._logger.debug('%s -> Lesson Plan' % self._current_view)
        self._canvas.set_root(self._lessonplan_canvas())
        self.show_all()

    def _button_closelessonplan_cb(self, button, lesson_return):
        """Lesson Plan button clicked in Lesson Plan view.
        
        Go back to the view we had previously.
        """
        self._logger.debug('Lesson plans -> %s' % lesson_return)
        if lesson_return == 'poll':
            self._canvas.set_root(self._poll_canvas())
        elif lesson_return == 'select':
            self._canvas.set_root(self._select_canvas())
        elif lesson_return == 'build':
            self._canvas.set_root(self._build_canvas())
        self.show_all()

    def _size_answer_text(self, choice):
        """Choose font size for poll answers.

        choice -- integer to choose an answer.

        returns font size as integer.
        """
        text =  self.poll_options[choice]
        if len(text) <= 16:
            text_size = 12
        elif len(text) <= 18:
            text_size = 11
        elif len(text) <= 20:
            text_size = 10
        elif len(text) <= 22:
            text_size = 9
        elif len(text) <= 25:
            text_size = 8
        elif len(text) <= 29:
            text_size = 7
        elif len(text) <= 33:
            text_size = 6
        else:
            text_size = 5
        return text_size

    def _size_heading_text(self, text):
        """Choose font size for poll headings.

        text -- string of the title or question.

        returns font size as integer.
        """
        if len(text) <= 38:
            text_size = 12
        elif len(text) <= 55:
            text_size = 11
        elif len(text) <= 59:
            text_size = 10
        elif len(text) <= 65:
            text_size = 9
        elif len(text) <= 74:
            text_size = 8
        elif len(text) <= 80:
            text_size = 7
        elif len(text) <= 90:
            text_size = 6
        else:
            text_size = 5
        return text_size

    def _canvas_mainbox(self):
        mainbox = hippo.CanvasBox(spacing=4,
            background_color=color.HTMLColor(LIGHT_GREEN).get_int(),
            border=4,
            border_color=color.HTMLColor(YELLOW).get_int(),
            padding_top=20, padding_left=40, padding_right=40,
            padding_bottom=20,
            orientation=hippo.ORIENTATION_VERTICAL)
        return mainbox

    def _text_mainbox(self, text, warn=False):
        """Main text style.
        
        warn=True makes the text color RED and appends ???.
        """
        if warn:
            text_color = RED
            text = text + '???'
        else:
            text_color = DARK_GREEN
        return hippo.CanvasText(
            text=text,
            xalign=hippo.ALIGNMENT_START,
            font_desc = pango.FontDescription('Sans 12'),
            color=color.HTMLColor(text_color).get_int())

    def _canvas_buttonbox(self, button_to_highlight=None):
        button_box = hippo.CanvasBox(
            spacing=8,
            padding=8,
            orientation=hippo.ORIENTATION_HORIZONTAL)
        button = gtk.Button(_("Build a Poll"))
        button.connect('clicked', self.button_new_clicked)
        button_box.append(hippo.CanvasWidget(
            widget=theme_button(button,
                               highlight=(button_to_highlight==1))))
        button = gtk.Button(_("Choose a Poll"))
        button.connect('clicked', self.button_select_clicked)
        button_box.append(hippo.CanvasWidget(
            widget=theme_button(button,
                               highlight=(button_to_highlight==2))))
        return button_box

    def _shared_cb(self, activity):
        """Callback for completion of sharing this activity."""
        self._logger.debug('My activity was shared')
        self.initiating = True
        self._setup()

        for buddy in self._shared_activity.get_joined_buddies():
            self._logger.debug('Buddy %s is already in the activity' %
                buddy.props.nick)

        self._shared_activity.connect('buddy-joined', self._buddy_joined_cb)
        self._shared_activity.connect('buddy-left', self._buddy_left_cb)

        self._logger.debug('This is my activity: making a tube...')
        id = self.tubes_chan[telepathy.CHANNEL_TYPE_TUBES].OfferTube(
            telepathy.TUBE_TYPE_DBUS, SERVICE, {})

    def _setup(self):
        """Setup my Tubes channel.
        
        Called from _shared_cb or _joined_cb.
        """
        if self._shared_activity is None:
            self._logger.error('Failed to share or join activity')
            return

        bus_name, conn_path, channel_paths =\
            self._shared_activity.get_channels()

        # Work out what our room is called and whether we have Tubes already
        room = None
        tubes_chan = None
        text_chan = None
        for channel_path in channel_paths:
            channel = telepathy.client.Channel(bus_name, channel_path)
            htype, handle = channel.GetHandle()
            if htype == telepathy.HANDLE_TYPE_ROOM:
                self._logger.debug('Found our room: it has handle#%d "%s"',
                    handle, self.conn.InspectHandles(htype, [handle])[0])
                room = handle
                ctype = channel.GetChannelType()
                if ctype == telepathy.CHANNEL_TYPE_TUBES:
                    self._logger.debug('Found our Tubes channel at %s', channel_path)
                    tubes_chan = channel
                elif ctype == telepathy.CHANNEL_TYPE_TEXT:
                    self._logger.debug('Found our Text channel at %s', channel_path)
                    text_chan = channel

        if room is None:
            self._logger.error("Presence service didn't create a room")
            return
        if text_chan is None:
            self._logger.error("Presence service didn't create a text channel")
            return

        # Make sure we have a Tubes channel - PS doesn't yet provide one
        if tubes_chan is None:
            self._logger.debug("Didn't find our Tubes channel, requesting one...")
            tubes_chan = self.conn.request_channel(telepathy.CHANNEL_TYPE_TUBES,
                telepathy.HANDLE_TYPE_ROOM, room, True)

        self.tubes_chan = tubes_chan
        self.text_chan = text_chan

        tubes_chan[telepathy.CHANNEL_TYPE_TUBES].connect_to_signal('NewTube',
            self._new_tube_cb)

    def _list_tubes_reply_cb(self, tubes):
        for tube_info in tubes:
            self._new_tube_cb(*tube_info)

    def _list_tubes_error_cb(self, e):
        self._logger.error('ListTubes() failed: %s', e)

    def _joined_cb(self, activity):
        """Callback for completion of joining the activity."""
        if not self._shared_activity:
            return

        # Find out who's already in the shared activity:
        for buddy in self._shared_activity.get_joined_buddies():
            self._logger.debug('Buddy %s is already in the activity' % buddy.props.nick)

        self._logger.debug('Joined an existing shared activity')
        self.initiating = False
        self._setup()

        self._logger.debug('This is not my activity: waiting for a tube...')
        self.tubes_chan[telepathy.CHANNEL_TYPE_TUBES].ListTubes(
            reply_handler=self._list_tubes_reply_cb,
            error_handler=self._list_tubes_error_cb)

    def _new_tube_cb(self, id, initiator, type, service, params, state):
        """Callback for when we have a Tube."""
        self._logger.debug('New tube: ID=%d initator=%d type=%d service=%s '
                     'params=%r state=%d', id, initiator, type, service,
                     params, state)

        if (type == telepathy.TUBE_TYPE_DBUS and
            service == SERVICE):
            if state == telepathy.TUBE_STATE_LOCAL_PENDING:
                self.tubes_chan[telepathy.CHANNEL_TYPE_TUBES].AcceptTube(id)

            tube_conn = TubeConnection(self.conn,
                self.tubes_chan[telepathy.CHANNEL_TYPE_TUBES],
                id, group_iface=self.text_chan[telepathy.CHANNEL_INTERFACE_GROUP])
            self.poll_session = PollSession(tube_conn, self.initiating, self._get_buddy, self)

    def _buddy_joined_cb (self, activity, buddy):
        self._logger.debug('Buddy %s joined' % buddy.props.nick)

    def _buddy_left_cb (self, activity, buddy):
        self._logger.debug('Buddy %s left' % buddy.props.nick)

    def _get_buddy(self, cs_handle):
        """Get a Buddy from a channel specific handle."""
        self._logger.debug('Trying to find owner of handle %u...', cs_handle)
        group = self.text_chan[telepathy.CHANNEL_INTERFACE_GROUP]
        my_csh = group.GetSelfHandle()
        self._logger.debug('My handle in that group is %u', my_csh)
        if my_csh == cs_handle:
            handle = self.conn.GetSelfHandle()
            self._logger.debug('CS handle %u belongs to me, %u', cs_handle, handle)
        elif group.GetGroupFlags() & telepathy.CHANNEL_GROUP_FLAG_CHANNEL_SPECIFIC_HANDLES:
            handle = group.GetHandleOwners([cs_handle])[0]
            self._logger.debug('CS handle %u belongs to %u', cs_handle, handle)
        else:
            handle = cs_handle
            logger.debug('non-CS handle %u belongs to itself', handle)

            # XXX: deal with failure to get the handle owner
            assert handle != 0

        # XXX: we're assuming that we have Buddy objects for all contacts -
        # this might break when the server becomes scalable.
        return self.pservice.get_buddy_by_telepathy_handle(self.tp_conn_name,
                self.tp_conn_path, handle)


class PollSession(ExportedGObject):
    """The bit that talks over the TUBES!!!"""

    def __init__(self, tube, is_initiator, get_buddy, activity):
        """Initialise the PollSession.

        tube -- TubeConnection
        is_initiator -- boolean, True = we are sharing, False = we are joining
        get_buddy -- function
        activity -- PollBuilder (sugar.activity.Activity)
        """
        super(PollSession, self).__init__(tube, PATH)
        self._logger = logging.getLogger('poll-activity.PollSession')
        self.tube = tube
        self.is_initiator = is_initiator
        self.entered = False  # Have we set up the tube?
        self._get_buddy = get_buddy  # Converts handle to Buddy object
        self.activity = activity  # PollBuilder
        self.tube.watch_participants(self.participant_change_cb)

    def participant_change_cb(self, added, removed):
        """Callback when tube participants change."""
        self._logger.debug('Adding participants: %r' % added)
        self._logger.debug('Removing participants: %r' % removed)
        for handle, bus_name in added:
            buddy = self._get_buddy(handle)
            if buddy is not None:
                self._logger.debug('Buddy %s was added' % buddy.props.nick)
        for handle in removed:
            buddy = self._get_buddy(handle)
            if buddy is not None:
                self._logger.debug('Buddy %s was removed' % buddy.props.nick)
            try:
                self.ordered_bus_names.remove(self.tube.participants[handle])
            except ValueError:
                # already absent
                pass
        if not self.entered:
            #self.tube.add_signal_receiver(self.insert_cb, 'Insert', IFACE,
            #    path=PATH, sender_keyword='sender')
            if self.is_initiator:
                self._logger.debug("I'm initiating the tube, will "
                    "watch for hellos.")
                self.add_hello_handler()
                self.ordered_bus_names = [self.tube.get_unique_name()]
            else:
                self._logger.debug('Hello, everyone! What did I miss?')
                self.Hello()
        self.entered = True



def justify(textdict, choice):
    """Take a {} of numbers, and right justify the chosen item.

    textdict is a dict of {n: m} where n and m are integers.
    choice is one of textdict.keys()

    Returns a string of '   m' with m right-justified
    so that the longest value in the dict can fit.
    """
    max_len = 0
    for num in textdict.values():
        if len(str(num)) > max_len:
            max_len = len(str(num))
    value = str(textdict[choice])
    return value.rjust(max_len)


class LessonPlanWidget (gtk.Notebook):
    def __init__ (self, basepath):
        super(LessonPlanWidget, self).__init__()
        lessons = filter(lambda x: os.path.isdir(os.path.join(basepath, 'lessons', x)), os.listdir(os.path.join(basepath, 'lessons')))
        lessons.sort()
        for lesson in lessons:
            self._load_lesson(os.path.join(basepath, 'lessons', lesson), _(lesson))

    def _load_lesson (self, path, name):
        code, encoding = locale.getdefaultlocale()
        canvas = AbiCanvas()
        canvas.show()
        files = map(lambda x: os.path.join(path, '%s.abw' % x),
                    ('_'+code.lower(), '_'+code.split('_')[0].lower(), 'default'))
        files = filter(lambda x: os.path.exists(x), files)
        # On jhbuild, the first works, on XO the second works:
        try:
            canvas.load_file('file://%s' % files[0], 'text/plain')
        except:
            canvas.load_file('file://%s' % files[0])
        canvas.view_online_layout()
        canvas.zoom_width()
        canvas.set_show_margin(False)
        self.append_page(canvas, gtk.Label(name))
