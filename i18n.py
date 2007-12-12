#!/usr/bin/env python
# -*- coding: utf-8 -*-

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
#


### SliderPuzzeUI
### TODO: Describe
### $Id: $
###
### author: Carlos Neves (cn (at) sueste.net)
### (c) 2007 World Wide Workshop Foundation

import os
import gettext
import locale

import gtk, gobject

_ = lambda x: x

# Images were taken from http://www.sodipodi.com/ 
# except for korea taken from http://zh.wikipedia.org/wiki/Image:Unification_flag_of_Korea.svg

lang_name_mapping = {
    'zh_cn':(None, _('Chinese (simplified)'), 'china'),
    'zh_tw':(None, _('Chinese (traditional)'), 'china'),
    'cs':(None, _('Czech'),'czech_republic'),
    'da':(None, _('Danish'),'denmark'),
    'nl':(None, _('Dutch'), 'netherlands'),
    'en':('English', _('English'),'united_states'),
    'en_gb':('English', _('English - Great Britain'),'united_kingdom'),
    'en_us':('English', _('English - U.S.'),'united_states'),
    'fi':(None, _('Finnish'),'finland'),
    'fr':('Français', _('French'),'france'),
    'de':(None, _('German'),'germany'),
    'hu':(None, _('Hungarian'),'hungary'),
    'it':(None, _('Italian'),'italy'),
    'ja':(None, _('Japanese'),'japan'),
    'ko':(None, _('Korean'),'korea'),
    'no':(None, _('Norwegian'),'norway'),
    'pl':(None, _('Polish'),'poland'),
    'pt':('Português', _('Portuguese'),'portugal'),
    'pt_br':('Português do Brasil', _('Portuguese - Brazilian'),'brazil'),
    'ru':(None, _('Russian'),'russian_federation'),
    'sk':(None, _('Slovak'),'slovenia'),
    'es':('Español', _('Spanish'),'spain'),
    'sv':(None, _('Swedish'),'sweden'),
    'tr':(None, _('Turkish'),'turkey'),
    }

class LangDetails (object):
    def __init__ (self, code, name, image):
        self.code = code
        self.country_code = self.code.split('_')[0]
        self.name = name
        self.image = image

    def guess_translation (self, fallback=False):
        self.gnutranslation = gettext.translation('org.worldwideworkshop.olpc.SliderPuzzle', 'locale', [self.code], fallback=fallback)

    def install (self):
        self.gnutranslation.install()

    def matches (self, code, exact=True):
        if exact:
            return code.lower() == self.code.lower()
        return code.split('_')[0].lower() == self.country_code.lower()

def get_lang_details (lang):
    mapping = lang_name_mapping.get(lang.lower(), None)
    if mapping is None:
        # Try just the country code
        lang = lang.split('_')[0]
        mapping = lang_name_mapping.get(lang.lower(), None)
        if mapping is None:
            return None
    if mapping[0] is None:
        return LangDetails(lang, mapping[1], mapping[2])
    return LangDetails(lang, mapping[0], mapping[2])

def list_available_translations ():
    rv = [get_lang_details('en')]
    rv[0].guess_translation(True)
    for i,x in enumerate([x for x in os.listdir('locale') if os.path.isdir('locale/' + x) and not x.startswith('.')]):
        try:
            details = get_lang_details(x)
            if details is not None:
                details.guess_translation()
                rv.append(details)
        except:
            raise
            pass
    return rv

class LanguageComboBox (gtk.ComboBox):
    def __init__ (self):
        liststore = gtk.ListStore(gobject.TYPE_STRING)
        gtk.ComboBox.__init__(self, liststore)

        self.cell = gtk.CellRendererText()
        self.pack_start(self.cell, True)
        self.add_attribute(self.cell, 'text', 0)

        self.translations = list_available_translations()
        for i,x in enumerate(self.translations):
            liststore.insert(i+1, (gettext.gettext(x.name), ))
        self.connect('changed', self.install)

    def modify_bg (self, state, color):
        setattr(self.cell, 'background-gdk',color)
        setattr(self.cell, 'background-set',True)

    def install (self, *args):
        if self.get_active() > -1:
            self.translations[self.get_active()].install()
        else:
            code, encoding = locale.getdefaultlocale()
            # Handle default locale of None:
            if code is None:
                self.set_active(0)
            if self.get_active() < 0:
                # Try to find the exact translation
                for i,t in enumerate(self.translations):
                    if t.matches(code):
                        self.set_active(i)
                        break
            if self.get_active() < 0:
                # Failed, try to get the translation based only in the country
                for i,t in enumerate(self.translations):
                    if t.matches(code, False):
                        self.set_active(i)
                        break
            if self.get_active() < 0:
                # nothing found, select first translation
                self.set_active(0)
        # Allow for other callbacks
        return False

###
def gather_other_translations ():
    from glob import glob
    entries = filter(lambda x: os.path.isdir(x), glob('images/*'))
    entries.extend(filter(lambda x: os.path.isdir(x), glob('lessons/*')))
    entries = map(lambda x: os.path.basename(x), entries)
    f = file('i18n_misc_strings.py', 'w')
    for e in entries:
        f.write('_("%s")\n' % e)
    f.close()

if __name__ == '__main__':
    gather_other_translations()
