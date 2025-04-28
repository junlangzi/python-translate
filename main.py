

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, font as tkfont, simpledialog
import ttkbootstrap as tb
from ttkbootstrap.constants import *
from ttkbootstrap.dialogs import Messagebox
import os
import json
import tokenize
import io
import threading
import google.generativeai as genai
from google.api_core import exceptions as google_exceptions
from langdetect import detect, LangDetectException
import time
from pathlib import Path
import re
import ast
import traceback
import string
import subprocess
import tempfile
from tkinter.scrolledtext import ScrolledText

CONFIG_FILE = "translator_config.json"
DEFAULT_SETTINGS = {
    "theme": "solar",
    "window_size": "1400x1000",
    "font_family": "Segoe UI",
    "font_size": 10,
    "gemini_api_key": "",
    "target_languages": [
        "en",
        "vi",
        "es",
        "fr",
        "de",
        "zh-cn",
        "ja",
        "ko",
        "ru",
        "pt",
        "it",
        "ar",
        "hi",
        "af",
        "sq",
        "am",
        "hy",
        "az",
        "eu",
        "be",
        "bn",
        "bs",
        "bg",
        "ca",
        "ceb",
        "ny",
        "zh-tw",
        "co",
        "hr",
        "cs",
        "da",
        "nl",
        "eo",
        "et",
        "tl",
        "fi",
        "fy",
        "gl",
        "ka",
        "el",
        "gu",
        "ht",
        "ha",
        "haw",
        "iw",
        "hu",
        "is",
        "ig",
        "id",
        "ga",
        "jw",
        "kn",
        "kk",
        "km",
        "rw",
        "ku",
        "ky",
        "lo",
        "la",
        "lv",
        "lt",
        "lb",
        "mk",
        "mg",
        "ms",
        "ml",
        "mt",
        "mi",
        "mr",
        "mn",
        "my",
        "ne",
        "no",
        "or",
        "ps",
        "fa",
        "pl",
        "pa",
        "ro",
        "sm",
        "gd",
        "sr",
        "st",
        "sn",
        "sd",
        "si",
        "sk",
        "sl",
        "so",
        "su",
        "sw",
        "sv",
        "tg",
        "ta",
        "tt",
        "te",
        "th",
        "tr",
        "tk",
        "uk",
        "ur",
        "ug",
        "uz",
        "xh",
        "yi",
        "yo",
        "zu"
    ],
    "default_target_lang": "vi",
    "batch_size": 30,
    "rpm_limit": 10,
    "max_batch_retries": 2,
    "max_item_retries": 2,
    "retry_delay_seconds": 5,
    "string_translation_mode": "safe_ast",
    "verify_syntax_after_save": True,
    "max_verification_attempts": 5,
    "use_gemini_scan": False
}

MAX_BATCH_RETRIES = DEFAULT_SETTINGS["max_batch_retries"]
MAX_ITEM_RETRIES = DEFAULT_SETTINGS["max_item_retries"]
RETRY_DELAY_SECONDS = DEFAULT_SETTINGS["retry_delay_seconds"]
VERIFY_SYNTAX = DEFAULT_SETTINGS["verify_syntax_after_save"]
MAX_VERIFICATION_ATTEMPTS = DEFAULT_SETTINGS["max_verification_attempts"]


API_KEY_FROM_ENV = os.environ.get("GEMINI_API_KEY")

def add_parent_pointers(node):
    """Recursively adds a .parent attribute to each node in the AST."""
    for child in ast.iter_child_nodes(node):
        child.parent = node
        add_parent_pointers(child)

def is_likely_technical_string(text: str) -> bool:
    """
    Checks the content of a string to see if it looks like technical data,
    code identifiers, paths, etc., rather than natural language.
    Returns True if likely technical, False otherwise.
    """
    text = text.strip()
    if not text:
        return True

    if len(text) <= 2 and not text.isalnum():
        return True

    if re.fullmatch(r'[A-Z_][A-Z0-9_]*', text) and len(text) > 1:
        return True

    if '/' in text or '\\' in text:
        if re.search(r'[/\\][\w.-]+(\.\w+)?$', text) or text.startswith(('./', '../', '/', 'C:\\', '\\\\')):
             if text.count(' ') < 3:
                  return True

    if re.match(r'(?:https?|ftp)://', text, re.IGNORECASE):
        return True

    non_alnum_symbols = re.sub(r'[\w\s.,!?;:\'"()\[\]-]', '', text)
    if len(non_alnum_symbols) > len(text) * 0.3:
        return True
    if re.search(r'[][{}<>%=*+/^&|~]', text):
         if len(re.findall(r'[][{}<>%=*+/^&|~]', text)) > 2 or text.count(' ') == 0:
              return True

    sql_keywords = {'SELECT', 'INSERT', 'UPDATE', 'DELETE', 'FROM', 'WHERE', 'GROUP BY', 'ORDER BY', 'JOIN', 'CREATE', 'ALTER', 'DROP'}
    words = set(text.upper().split())
    if len(words.intersection(sql_keywords)) >= 2:
        return True

    if re.search(r'<[^>]+>', text):
        return True

    technical_terms = {
        'True', 'False', 'None', 'self', 'cls', 'def', 'class', 'lambda',
        'utf-8', 'ascii', 'str', 'int', 'float', 'list', 'dict', 'tuple', 'set',
        'args', 'kwargs', 'return', 'yield', 'import', 'from', 'as',
        'try', 'except', 'finally', 'raise', 'assert', 'with', 'pass', 'break', 'continue',
        '__init__', '__main__', 'GET', 'POST', 'PUT', 'DELETE', 'HEAD', 'OPTIONS',
        'application/json', 'text/html', 'px', 'em', 'rem', '%'
    }
    text_words = set(re.findall(r'\b\w+\b', text))
    if text in technical_terms or (len(text_words) > 0 and text_words.issubset(technical_terms)):
         return True
    if len(text_words) <= 2 and len(text_words.intersection(technical_terms)) > 0:
         return True

    return False

def is_meaningless_string(text: str) -> bool:
    """
    Checks if a string contains NO alphabetic characters.
    Returns True if it only contains punctuation, symbols, digits, whitespace.
    Returns False if it contains at least one letter.
    """
    if not text:
        return True
    return not any(char.isalpha() for char in text)

class TranslatableStringVisitor(ast.NodeVisitor):
    TRANSLATABLE_FUNC_NAMES = {
        'print', 'input', 'warning', 'error', 'info', 'log', 'exception', 'critical',
        'show_info', 'show_warning', 'show_error', 'ask_question', 'ask_ok_cancel',
        'ask_yes_no', 'Error', 'Warning', 'Exception', 'ValueError', 'TypeError',
        'RuntimeError', 'LookupError', 'IndexError',
        'QLabel', 'QPushButton', 'QCheckBox', 'QRadioButton', 'QAction',
        'Label', 'Button', 'Checkbutton', 'Radiobutton',
        'Messagebox', 'messagebox',
        '_', 'gettext', 'ngettext'
    }
    TRANSLATABLE_METHOD_NAMES = {
        'config', 'configure', 'set', 'setText', 'set_text', 'setLabelText',
        'setToolTip', 'setStatusTip', 'setWindowTitle', 'setPlaceholderText',
        'addItem', 'insertItem', 'append', 'show_message', 'show_info',
        'show_warning', 'show_error', 'show_question',
        'tr', 'translate',
        'setTitle', 'setMessage', 'setLabel', 'setTextValue'
    }
    TRANSLATABLE_KEYWORD_ARGS = {
        'text', 'message', 'title', 'label', 'caption', 'placeholder',
        'tooltip', 'whatsthis', 'statusTip', 'msg', 'detail', 'header', 'name'
    }
    NON_TRANSLATABLE_FUNC_METHOD_NAMES = {
        'open', 'eval', 'exec', 'compile', 'getattr', 'setattr', 'hasattr',
        '__import__', 'globals', 'locals', 'join', 'execute', 'connect',
        'read', 'write', 'encode', 'decode', 'get', 'post', 'put', 'delete',
        'match', 'search', 'findall', 'sub', 'split',
        'register', 'unregister', 'bind', 'unbind',
        'get', 'set', 'has',
        'startswith', 'endswith',
        'replace'
    }
    def __init__(self):
        self.translatable_nodes = {}
    def visit_Constant(self, node):
        if isinstance(node.value, str) and hasattr(node, 'parent'):
            string_value = node.value; parent = node.parent
            is_translatable_by_context = False
            if isinstance(parent, ast.Call) and node in parent.args:
                func = parent.func; func_name = None
                if isinstance(func, ast.Name): func_name = func.id
                elif isinstance(func, ast.Attribute): func_name = func.attr
                if func_name and func_name not in self.NON_TRANSLATABLE_FUNC_METHOD_NAMES:
                     if func_name in self.TRANSLATABLE_FUNC_NAMES or func_name in self.TRANSLATABLE_METHOD_NAMES:
                          is_translatable_by_context = True
            elif isinstance(parent, ast.keyword) and node == parent.value:
                if parent.arg in self.TRANSLATABLE_KEYWORD_ARGS:
                    grandparent = getattr(parent, 'parent', None)
                    if isinstance(grandparent, ast.Call):
                        func = grandparent.func; func_name = None
                        if isinstance(func, ast.Name): func_name = func.id
                        elif isinstance(func, ast.Attribute): func_name = func.attr
                        if not (func_name and func_name in self.NON_TRANSLATABLE_FUNC_METHOD_NAMES):
                            is_translatable_by_context = True
            elif isinstance(parent, ast.Raise):
                exc_call = parent.exc
                if isinstance(exc_call, ast.Call) and node in exc_call.args:
                     is_translatable_by_context = True
            if not is_translatable_by_context:
                 if isinstance(parent, ast.Dict) and node in parent.keys: is_translatable_by_context = False
                 elif isinstance(parent, (ast.FormattedValue, ast.JoinedStr)): is_translatable_by_context = False
                 elif isinstance(parent, ast.Compare) and node in parent.comparators: is_translatable_by_context = False
                 elif isinstance(parent, ast.Call) and node in parent.args:
                     func = parent.func; func_name = None
                     if isinstance(func, ast.Name): func_name = func.id
                     if func_name in ['getattr', 'setattr', 'hasattr']: is_translatable_by_context = False
                 elif isinstance(parent, ast.Subscript) and node == parent.slice: is_translatable_by_context = False
            if is_translatable_by_context:
                self.translatable_nodes[node.lineno] = (node, string_value)
        self.generic_visit(node)
    def visit_Str(self, node):
        if hasattr(node, 'lineno'):
            dummy_constant = ast.Constant(value=node.s, lineno=node.lineno, col_offset=node.col_offset)
            if hasattr(node, 'parent'): dummy_constant.parent = node.parent
            self.visit_Constant(dummy_constant)
        else: self.generic_visit(node)

class PythonTranslatorApp(tk.Tk):
    def __init__(self):
        self.settings = self.load_settings()
        global MAX_BATCH_RETRIES, MAX_ITEM_RETRIES, RETRY_DELAY_SECONDS, VERIFY_SYNTAX, MAX_VERIFICATION_ATTEMPTS
        MAX_BATCH_RETRIES = self.settings.get("max_batch_retries", DEFAULT_SETTINGS["max_batch_retries"])
        MAX_ITEM_RETRIES = self.settings.get("max_item_retries", DEFAULT_SETTINGS["max_item_retries"])
        RETRY_DELAY_SECONDS = self.settings.get("retry_delay_seconds", DEFAULT_SETTINGS["retry_delay_seconds"])
        VERIFY_SYNTAX = self.settings.get("verify_syntax_after_save", DEFAULT_SETTINGS["verify_syntax_after_save"])
        MAX_VERIFICATION_ATTEMPTS = self.settings.get("max_verification_attempts", DEFAULT_SETTINGS["max_verification_attempts"])

        self.current_theme = self.settings.get("theme", DEFAULT_SETTINGS["theme"])
        super().__init__()
        try:
            self.style = tb.Style(theme=self.current_theme)
        except tk.TclError:
             print(f"Warning: Theme '{self.current_theme}' not found. Falling back.")
             self.current_theme = "litera"; self.settings["theme"] = self.current_theme
             self.style = tb.Style(theme=self.current_theme)

        self.title("Python Code Translator & Comment Manager")
        self.geometry(self.settings.get("window_size", DEFAULT_SETTINGS["window_size"]))

        self.source_file_path = tk.StringVar()
        self.target_lang = tk.StringVar(value=self.settings.get("default_target_lang", DEFAULT_SETTINGS["default_target_lang"]))
        self.detected_source_lang = tk.StringVar(value="N/A")
        self.translation_data = []
        self.comment_data = []
        self.gemini_api_key = self.settings.get("gemini_api_key", "") or API_KEY_FROM_ENV or ""
        self.last_api_call_time = 0
        self.is_translating = False; self.is_paused = False; self.stop_flag = False
        self.scan_complete = False
        self.scan_produced_strings = False
        self.batch_size = self.settings.get("batch_size", DEFAULT_SETTINGS["batch_size"])
        self.rpm_limit = self.settings.get("rpm_limit", DEFAULT_SETTINGS["rpm_limit"])
        self.seconds_per_request = 60.0 / self.rpm_limit if self.rpm_limit > 0 else 0

        self.gemini_model = None
        if self.gemini_api_key: self.configure_gemini()

        self.app_font = None
        self.update_global_font()

        self.string_translation_mode_var = tk.StringVar(value=self.settings.get("string_translation_mode", DEFAULT_SETTINGS["string_translation_mode"]))
        self.verify_syntax_var = tk.BooleanVar(value=VERIFY_SYNTAX)
        self.use_gemini_scan_var = tk.BooleanVar(value=self.settings.get("use_gemini_scan", DEFAULT_SETTINGS["use_gemini_scan"]))
        self.auto_exclude_comments_var = tk.BooleanVar(value=False)

        self.ids_excluded_by_comment_filter = set()

        self.create_widgets()
        self.update_api_key_info()

    def configure_gemini(self):
        if not self.gemini_api_key:
            self.gemini_model = None; return False
        try:
            genai.configure(api_key=self.gemini_api_key)
            self.gemini_model = genai.GenerativeModel('gemini-1.5-flash')
            print("Gemini configured successfully."); return True
        except Exception as e:
            print(f"Error configuring Gemini API: {e}")
            self.gemini_model = None
            if hasattr(self, 'winfo_exists') and self.winfo_exists():
                 Messagebox.show_error(f"Lỗi cấu hình Gemini API:\n{e}", "Lỗi API", parent=self)
            return False

    def update_global_font(self):
        family = self.settings.get("font_family", DEFAULT_SETTINGS["font_family"])
        size = self.settings.get("font_size", DEFAULT_SETTINGS["font_size"])
        try:
            self.app_font = tkfont.Font(family=family, size=size)
            row_padding = 4; linespace = self.app_font.metrics('linespace')
            dynamic_row_height = linespace + row_padding
            self.style.configure('.', font=self.app_font)
            self.style.configure('Treeview.Heading', font=(family, size, 'bold'))
            self.style.configure('Treeview', rowheight=dynamic_row_height, font=self.app_font)
            if hasattr(self, 'tree_trans'): self.tree_trans.configure(style='Treeview')
            if hasattr(self, 'tree_comments'): self.tree_comments.configure(style='Treeview')
        except tk.TclError as e:
            print(f"Error setting font: {e}. Using default.")

    def hide_initial_help(self):
        """Hides the initial help label if it exists and is visible."""
        if hasattr(self, 'initial_help_label') and self.initial_help_label.winfo_ismapped():
            self.initial_help_label.grid_remove()

    def create_widgets(self):
        main_frame = tb.Frame(self, padding=15); main_frame.pack(fill=BOTH, expand=True)
        self.notebook = ttk.Notebook(main_frame); self.notebook.pack(fill=BOTH, expand=True, pady=(0, 10))

        translator_frame = tb.Frame(self.notebook, padding=10); self.notebook.add(translator_frame, text="💻 Python Translate")
        translator_frame.rowconfigure(4, weight=1)
        translator_frame.columnconfigure(0, weight=1)

        top_frame = tb.Frame(translator_frame); top_frame.grid(row=0, column=0, sticky=EW, pady=(0, 10))
        top_frame.columnconfigure(0, weight=1)

        file_options_frame = tb.Labelframe(top_frame, text="📂File & Tùy chọn", padding=10)
        file_options_frame.grid(row=0, column=0, sticky=EW, padx=(0, 10))
        file_options_frame.columnconfigure(1, weight=1)
        btn_select = tb.Button(file_options_frame, text="📂 Python file...", command=self.select_file, bootstyle=PRIMARY)
        btn_select.grid(row=0, column=0, padx=5, pady=5, sticky=W)
        lbl_file = tb.Label(file_options_frame, textvariable=self.source_file_path, relief=SUNKEN, padding=5, width=60)
        lbl_file.grid(row=0, column=1, padx=5, pady=5, sticky=EW)
        lang_frame = tb.Frame(file_options_frame)
        lang_frame.grid(row=1, column=0, columnspan=2, pady=5, sticky=W+N)
        lbl_target_lang = tb.Label(lang_frame, text="🔁Dịch sang:")
        lbl_target_lang.pack(side=LEFT, padx=(0, 5), anchor=W)
        combo_target_lang = tb.Combobox(lang_frame, textvariable=self.target_lang, values=self.settings.get("target_languages", DEFAULT_SETTINGS["target_languages"]), state="readonly", width=5)
        combo_target_lang.pack(side=LEFT, padx=(0, 20), anchor=W)
        lbl_source_lang = tb.Label(lang_frame, text="Ngôn ngữ gốc (auto):")
        lbl_source_lang.pack(side=LEFT, padx=(0, 5), anchor=W)
        lbl_detected_lang = tb.Label(lang_frame, textvariable=self.detected_source_lang, width=15, style='info.TLabel', anchor=W)
        lbl_detected_lang.pack(side=LEFT, anchor=W)
        string_options_frame = tb.Frame(file_options_frame)
        string_options_frame.grid(row=2, column=0, columnspan=2, pady=5, sticky=W)
        lbl_string_mode = tb.Label(string_options_frame, text="Dịch chuỗi ký tự (Strings):")
        lbl_string_mode.pack(side=LEFT, padx=(0, 5))
        rb_none = tb.Radiobutton(string_options_frame, text="Không dịch", variable=self.string_translation_mode_var, value="none", bootstyle=TOOLBUTTON)
        rb_none.pack(side=LEFT, padx=2)
        rb_safe = tb.Radiobutton(string_options_frame, text="An toàn (AST+Content)", variable=self.string_translation_mode_var, value="safe_ast", bootstyle=(TOOLBUTTON, INFO))
        rb_safe.pack(side=LEFT, padx=2)
        rb_all = tb.Radiobutton(string_options_frame, text="Tất cả (Nguy hiểm⚠️)", variable=self.string_translation_mode_var, value="all", bootstyle=(TOOLBUTTON, WARNING))
        rb_all.pack(side=LEFT, padx=2)


        action_frame = tb.Frame(top_frame)
        action_frame.grid(row=0, column=1, sticky=NS, padx=(5, 0))

        self.chk_gemini_scan = tb.Checkbutton(action_frame, variable=self.use_gemini_scan_var,
                                              text="🧠 Quét thông minh (Gemini)", bootstyle=PRIMARY)
        self.chk_gemini_scan.grid(row=0, column=0, columnspan=2, sticky=W, padx=5, pady=(0, 5))

        trans_action_buttons_frame = tb.Frame(action_frame)
        trans_action_buttons_frame.grid(row=1, column=0, columnspan=2, sticky=EW)

        btn_frame1 = tb.Frame(trans_action_buttons_frame)
        btn_frame1.grid(row=0, column=0, padx=5, pady=5, sticky=N)
        self.btn_translate = tb.Button(btn_frame1, text="Quét / Dịch", command=self.handle_scan_or_translate, bootstyle=(SUCCESS, OUTLINE), state=DISABLED, width=15)
        self.btn_translate.pack(pady=2)
        self.btn_pause_resume = tb.Button(btn_frame1, text="⏯Tạm dừng", command=self.toggle_pause, bootstyle=(WARNING, OUTLINE), state=DISABLED, width=15)
        self.btn_pause_resume.pack(pady=2)

        btn_frame2 = tb.Frame(trans_action_buttons_frame)
        btn_frame2.grid(row=0, column=1, padx=5, pady=5, sticky=N)
        self.btn_stop = tb.Button(btn_frame2, text="⏸Dừng", command=self.stop_translation, bootstyle=(DANGER, OUTLINE), state=DISABLED, width=15)
        self.btn_stop.pack(pady=2)
        self.btn_save_trans = tb.Button(btn_frame2, text="💾Lưu File Dịch", command=self.save_translated_file, bootstyle=(PRIMARY, OUTLINE), state=DISABLED, width=15)
        self.btn_save_trans.pack(pady=2)

        self.btn_run_test = tb.Button(btn_frame2, text="▶️Chạy thử", command=self.run_test_translation, bootstyle=(INFO, OUTLINE), state=DISABLED, width=15)
        self.btn_run_test.pack(pady=2)

        comment_action_frame = tb.Labelframe(translator_frame, text="✒️Quản lý Comment", padding=10)
        comment_action_frame.grid(row=1, column=0, sticky=EW, pady=(10, 5))

        self.btn_scan_comments = tb.Button(comment_action_frame, text="🔍Quét Comments", command=self.scan_comments, bootstyle=(INFO, OUTLINE), state=DISABLED, width=15)
        self.btn_scan_comments.pack(side=LEFT, padx=5, pady=5)

        self.btn_check_all_comments = tb.Button(comment_action_frame, text="☑️Check ALL", command=self.select_all_comments, bootstyle=(SUCCESS, OUTLINE), state=DISABLED, width=15)
        self.btn_check_all_comments.pack(side=LEFT, padx=5, pady=5)

        self.btn_uncheck_all_comments = tb.Button(comment_action_frame, text="☐Uncheck ALL", command=self.deselect_all_comments, bootstyle=(WARNING, OUTLINE), state=DISABLED, width=15)
        self.btn_uncheck_all_comments.pack(side=LEFT, padx=5, pady=5)

        self.btn_save_comments = tb.Button(comment_action_frame, text="💾Lưu Comments", command=self.save_comment_changes, bootstyle=(PRIMARY, OUTLINE), state=DISABLED, width=15)
        self.btn_save_comments.pack(side=LEFT, padx=5, pady=5)


        self.status_bar = tb.Label(translator_frame, text="Trạng thái: Sẵn sàng", anchor=W, padding=(5, 2))
        self.status_bar.grid(row=2, column=0, sticky=EW, pady=(5, 0))

        help_text = (
             "HƯỚNG DẪN SỬ DỤNG:\n\n"
             "1. QUẢN LÝ Comment:\n"
             "   - Chọn file Python. Bấm 'Quét Comments'. Nội dung sẽ hiển thị ở bảng dưới.\n"
             "   - Dùng 'Check ALL' / 'Uncheck ALL' hoặc nháy đúp vào dòng để Chọn giữ (☑) hoặc Bỏ chọn (☐).\n"
             "   - Nháy vào biểu tượng ✒️ ở cột 'Edit' để sửa nội dung comment.\n"
             "   - Bấm 'Lưu Comments' để lưu file mới, chỉ giữ lại các comment được đánh dấu ☑ (bao gồm cả nội dung đã sửa).\n\n"
             "2. DỊCH FILE PYTHON:\n"
             "   - Bật 'Quét thông minh (Gemini)' để AI gợi ý dòng cần dịch (không bắt buộc).\n"
             "   - Bấm 'Quét / Dịch' để quét nội dung.\n"
             "   - Xem lại danh sách, bỏ chọn (☐) các mục không muốn dịch. Dùng nút 'Chọn/Bỏ Chọn Tất cả' để thao tác nhanh.\n"
             "   - Chọn ngôn ngữ đích. Bấm 'Dịch'. Sau khi dịch xong, bấm 'Lưu File Dịch'.\n\n"
             "Chú ý:\n\n"
             "- Quét thông minh cần API Key Gemini và có thể tốn chi phí/quota.\n"
             "- Nếu dùng API Free, đặt giới hạn tốc độ < 15 request/phút trong Cài đặt.\n"
             "- Chế độ dịch chuỗi nên chọn 'An toàn (AST+Content)'.\n"
             "- Điền API Key Gemini của bạn (lấy từ https://aistudio.google.com/)."
         )
        self.initial_help_label = tb.Label(translator_frame, text=help_text, anchor=CENTER, wraplength=800, justify=CENTER, style='secondary.TLabel')
        self.initial_help_label.grid(row=3, column=0, sticky=EW, padx=5, pady=(0, 10))

        self.results_area_frame = tb.Frame(translator_frame, padding=(0, 5, 0, 0))
        self.results_area_frame.grid(row=4, column=0, sticky="nsew", pady=(5, 0))
        self.results_area_frame.rowconfigure(0, weight=1)
        self.results_area_frame.columnconfigure(0, weight=1)

        self.trans_result_frame = tb.Frame(self.results_area_frame)
        self.trans_result_frame.grid(row=0, column=0, sticky="nsew")
        self.trans_result_frame.rowconfigure(1, weight=1)
        self.trans_result_frame.columnconfigure(0, weight=1)

        trans_label_filter_frame = tb.Frame(self.trans_result_frame)
        trans_label_filter_frame.grid(row=0, column=0, columnspan=2, sticky=EW, pady=(0, 5))

        self.lbl_trans_results = tb.Label(trans_label_filter_frame, text="🔠Kết quả Dịch ", font=f"-size {self.settings['font_size']} -weight bold")
        self.lbl_trans_results.pack(side=LEFT, anchor=W, padx=(0,15))

        self.chk_auto_exclude_comments = tb.Checkbutton(
            trans_label_filter_frame,
            text="Bỏ qua #Comments",
            variable=self.auto_exclude_comments_var,
            command=self.apply_comment_filter,
            bootstyle=SECONDARY,
            state=DISABLED
        )
        self.chk_auto_exclude_comments.pack(side=LEFT, anchor=W, padx=(0,10))


        self.btn_select_all_trans = tb.Button(
            trans_label_filter_frame,
            text="☑️ALL",
            command=self.select_all_trans_items,
            bootstyle=(SUCCESS, SOLID),
            state=DISABLED,
            width=10
        )
        self.btn_select_all_trans.pack(side=LEFT, anchor=W, padx=(10, 5))

        self.btn_deselect_all_trans = tb.Button(
            trans_label_filter_frame,
            text="⛔ALL",
            command=self.deselect_all_trans_items,
            bootstyle=(WARNING, SOLID),
            state=DISABLED,
            width=10
        )
        self.btn_deselect_all_trans.pack(side=LEFT, anchor=W, padx=5)


        trans_columns = ("include", "line", "original", "status", "translated")
        self.tree_trans = tb.Treeview(self.trans_result_frame, columns=trans_columns, show="headings", selectmode="browse", style='Treeview')
        self.tree_trans.heading("include", text="Dịch?", anchor=CENTER); self.tree_trans.column("include", width=50, stretch=False, anchor=CENTER)
        self.tree_trans.heading("line", text="Dòng #", anchor=W); self.tree_trans.column("line", width=60, stretch=False, anchor=CENTER)
        self.tree_trans.heading("original", text="Nội dung Gốc", anchor=W); self.tree_trans.column("original", width=350, stretch=True)
        self.tree_trans.heading("status", text="Trạng thái", anchor=W); self.tree_trans.column("status", width=150, stretch=False, anchor=W)
        self.tree_trans.heading("translated", text="Nội dung Đã Dịch / Giữ lại", anchor=W); self.tree_trans.column("translated", width=350, stretch=True)
        tree_trans_scroll_y = tb.Scrollbar(self.trans_result_frame, orient=VERTICAL, command=self.tree_trans.yview, bootstyle=ROUND)
        tree_trans_scroll_x = tb.Scrollbar(self.trans_result_frame, orient=HORIZONTAL, command=self.tree_trans.xview, bootstyle=ROUND)
        self.tree_trans.configure(yscrollcommand=tree_trans_scroll_y.set, xscrollcommand=tree_trans_scroll_x.set)
        self.tree_trans.grid(row=1, column=0, sticky="nsew")
        tree_trans_scroll_y.grid(row=1, column=1, sticky="ns")
        tree_trans_scroll_x.grid(row=2, column=0, sticky="ew")
        self.tree_trans.bind("<Double-1>", self.toggle_translation_item_inclusion)

        self.comment_result_frame = tb.Frame(self.results_area_frame)
        self.comment_result_frame.grid(row=0, column=0, sticky="nsew")
        self.comment_result_frame.rowconfigure(1, weight=1)
        self.comment_result_frame.columnconfigure(0, weight=1)

        self.lbl_comment_results = tb.Label(self.comment_result_frame, text="Quản lý Comments (Nháy đúp để ☑/☐ | Nháy ✒️ để sửa)", font=f"-size {self.settings['font_size']} -weight bold")
        self.lbl_comment_results.grid(row=0, column=0, columnspan=2, sticky=W, pady=(0, 2))
        comment_columns = ("line", "comment", "edit", "keep")
        self.tree_comments = tb.Treeview(self.comment_result_frame, columns=comment_columns, show="headings", selectmode="browse", style='Treeview')
        self.tree_comments.heading("line", text="Dòng #", anchor=W); self.tree_comments.column("line", width=60, stretch=False, anchor=CENTER)
        self.tree_comments.heading("comment", text="Nội dung Comment", anchor=W); self.tree_comments.column("comment", width=550, stretch=True)
        self.tree_comments.heading("edit", text="Edit", anchor=CENTER); self.tree_comments.column("edit", width=40, stretch=False, anchor=CENTER)
        self.tree_comments.heading("keep", text="Giữ ☑", anchor=CENTER); self.tree_comments.column("keep", width=80, stretch=False, anchor=CENTER)
        comment_scroll_y = tb.Scrollbar(self.comment_result_frame, orient=VERTICAL, command=self.tree_comments.yview, bootstyle=ROUND)
        comment_scroll_x = tb.Scrollbar(self.comment_result_frame, orient=HORIZONTAL, command=self.tree_comments.xview, bootstyle=ROUND)
        self.tree_comments.configure(yscrollcommand=comment_scroll_y.set, xscrollcommand=comment_scroll_x.set)
        self.tree_comments.grid(row=1, column=0, sticky="nsew")
        comment_scroll_y.grid(row=1, column=1, sticky="ns")
        comment_scroll_x.grid(row=2, column=0, sticky="ew")
        self.tree_comments.bind("<Double-1>", self.handle_comment_double_click)
        self.tree_comments.bind("<Button-1>", self.handle_comment_single_click)

        settings_frame = tb.Frame(self.notebook, padding=10)
        self.notebook.add(settings_frame, text="⚙️Cài đặt")
        self.create_settings_tab(settings_frame)

        self.update_treeview_tags()
        self.update_global_font()

        self.trans_result_frame.grid_remove()
        self.comment_result_frame.grid_remove()

    def create_settings_tab(self, parent):
        frame = tb.Frame(parent, padding=20); frame.pack(fill=BOTH, expand=True); frame.columnconfigure(0, weight=1)
        theme_frame = tb.Labelframe(frame, text="Giao diện (Theme)", padding=10); theme_frame.grid(row=0, column=0, sticky=EW, pady=5)
        lbl_theme = tb.Label(theme_frame, text="Chọn Theme:"); lbl_theme.grid(row=0, column=0, padx=5, pady=5, sticky=W)
        self.temp_theme = tk.StringVar(value=self.settings.get("theme")); combo_theme = tb.Combobox(theme_frame, textvariable=self.temp_theme, values=sorted(self.style.theme_names()), state="readonly", width=20); combo_theme.grid(row=0, column=1, padx=5, pady=5, sticky=W)

        font_frame = tb.Labelframe(frame, text="Font chữ", padding=10); font_frame.grid(row=1, column=0, sticky=EW, pady=5)
        lbl_font_family = tb.Label(font_frame, text="Font Family:"); lbl_font_family.grid(row=0, column=0, padx=5, pady=5, sticky=W); available_fonts = sorted([f for f in tkfont.families() if not f.startswith('@')]); self.temp_font_family = tk.StringVar(value=self.settings.get("font_family")); combo_font_family = tb.Combobox(font_frame, textvariable=self.temp_font_family, values=available_fonts, state="readonly", width=25); combo_font_family.grid(row=0, column=1, padx=5, pady=5, sticky=W)
        lbl_font_size = tb.Label(font_frame, text="Cỡ chữ:"); lbl_font_size.grid(row=1, column=0, padx=5, pady=5, sticky=W); self.temp_font_size = tk.IntVar(value=self.settings.get("font_size")); spin_font_size = tb.Spinbox(font_frame, from_=8, to=24, increment=1, textvariable=self.temp_font_size, width=5); spin_font_size.grid(row=1, column=1, padx=5, pady=5, sticky=W)

        size_frame = tb.Labelframe(frame, text="Kích thước Cửa sổ", padding=10); size_frame.grid(row=2, column=0, sticky=EW, pady=5)
        lbl_size = tb.Label(size_frame, text="Nhập kích thước (VD: 1200x800):"); lbl_size.grid(row=0, column=0, padx=5, pady=5, sticky=W); self.temp_window_size = tk.StringVar(value=self.settings.get("window_size")); entry_size = tb.Entry(size_frame, textvariable=self.temp_window_size, width=15); entry_size.grid(row=0, column=1, padx=5, pady=5, sticky=W)

        trans_frame = tb.Labelframe(frame, text="Cài đặt Dịch & API", padding=10)
        trans_frame.grid(row=3, column=0, sticky=EW, pady=5)
        trans_frame.columnconfigure(1, weight=1)

        scan_mode_frame = tb.Frame(trans_frame)
        scan_mode_frame.grid(row=0, column=0, columnspan=4, padx=5, pady=5, sticky=W)
        self.temp_use_gemini_scan = tk.BooleanVar(value=self.settings.get("use_gemini_scan", DEFAULT_SETTINGS["use_gemini_scan"]))
        chk_gemini_mode = tb.Checkbutton(scan_mode_frame, text="Bật quét thông minh (Gemini) để xác định dòng (Cần API Key)",
                                          variable=self.temp_use_gemini_scan, bootstyle=PRIMARY)
        chk_gemini_mode.pack(side=LEFT, padx=(0, 10))

        str_mode_frame = tb.Frame(trans_frame); str_mode_frame.grid(row=1, column=0, columnspan=4, padx=5, pady=5, sticky=W)
        lbl_str_mode_set = tb.Label(str_mode_frame, text="Chế độ dịch chuỗi:"); lbl_str_mode_set.pack(side=LEFT, padx=(0, 5))
        self.temp_string_mode = tk.StringVar(value=self.settings.get("string_translation_mode", DEFAULT_SETTINGS["string_translation_mode"]))
        combo_str_mode = tb.Combobox(str_mode_frame, textvariable=self.temp_string_mode, values=["none", "safe_ast", "all"], state="readonly", width=10); combo_str_mode.pack(side=LEFT, padx=5)
        lbl_str_mode_desc = tb.Label(str_mode_frame, text="(None=Tắt, Safe=AST+Content, All=Tất cả)"); lbl_str_mode_desc.pack(side=LEFT, padx=5)


        lbl_batch_size = tb.Label(trans_frame, text="Số lượng dịch mỗi lần (batch):"); lbl_batch_size.grid(row=2, column=0, padx=5, pady=5, sticky=W)
        self.temp_batch_size = tk.IntVar(value=self.settings.get("batch_size")); spin_batch_size = tb.Spinbox(trans_frame, from_=1, to=100, increment=1, textvariable=self.temp_batch_size, width=5); spin_batch_size.grid(row=2, column=1, padx=5, pady=5, sticky=W)

        lbl_rpm_limit = tb.Label(trans_frame, text="Giới hạn tốc độ (request/phút):"); lbl_rpm_limit.grid(row=3, column=0, padx=5, pady=5, sticky=W)
        self.temp_rpm_limit = tk.IntVar(value=self.settings.get("rpm_limit")); spin_rpm_limit = tb.Spinbox(trans_frame, from_=1, to=100, increment=1, textvariable=self.temp_rpm_limit, width=5); spin_rpm_limit.grid(row=3, column=1, padx=5, pady=5, sticky=W)

        lbl_retries = tb.Label(trans_frame, text="Số lần thử lại khi lỗi API:"); lbl_retries.grid(row=4, column=0, padx=5, pady=5, sticky=W)
        retry_frame = tb.Frame(trans_frame); retry_frame.grid(row=4, column=1, columnspan=3, sticky=EW)
        lbl_batch_retry = tb.Label(retry_frame, text="Batch:"); lbl_batch_retry.pack(side=LEFT, padx=(0, 2)); self.temp_batch_retries = tk.IntVar(value=self.settings.get("max_batch_retries", DEFAULT_SETTINGS["max_batch_retries"])); spin_batch_retries = tb.Spinbox(retry_frame, from_=0, to=10, textvariable=self.temp_batch_retries, width=3); spin_batch_retries.pack(side=LEFT, padx=(0, 10))
        lbl_item_retry = tb.Label(retry_frame, text="Item:"); lbl_item_retry.pack(side=LEFT, padx=(0, 2)); self.temp_item_retries = tk.IntVar(value=self.settings.get("max_item_retries", DEFAULT_SETTINGS["max_item_retries"])); spin_item_retries = tb.Spinbox(retry_frame, from_=0, to=10, textvariable=self.temp_item_retries, width=3); spin_item_retries.pack(side=LEFT, padx=(0, 10))
        lbl_retry_delay = tb.Label(retry_frame, text="Delay(s):"); lbl_retry_delay.pack(side=LEFT, padx=(10, 2)); self.temp_retry_delay = tk.IntVar(value=self.settings.get("retry_delay_seconds", DEFAULT_SETTINGS["retry_delay_seconds"])); spin_retry_delay = tb.Spinbox(retry_frame, from_=1, to=60, textvariable=self.temp_retry_delay, width=3); spin_retry_delay.pack(side=LEFT, padx=(0, 5))

        lbl_api = tb.Label(trans_frame, text="Gemini API Key:"); lbl_api.grid(row=5, column=0, padx=5, pady=5, sticky=W)
        self.temp_api_key = tk.StringVar(value=self.gemini_api_key if not API_KEY_FROM_ENV else ""); self.entry_api = tb.Entry(trans_frame, textvariable=self.temp_api_key, width=40, show="*"); self.entry_api.grid(row=5, column=1, columnspan=3, padx=5, pady=5, sticky=EW)
        self.lbl_api_info = tb.Label(trans_frame, text="", font=(None, 8), wraplength=350); self.lbl_api_info.grid(row=6, column=0, columnspan=4, padx=5, sticky=W)

        verify_frame = tb.Frame(trans_frame)
        verify_frame.grid(row=7, column=0, columnspan=4, padx=5, pady=(10, 5), sticky=W)
        self.temp_verify_syntax = tk.BooleanVar(value=self.settings.get("verify_syntax_after_save", DEFAULT_SETTINGS["verify_syntax_after_save"]))
        chk_verify = tb.Checkbutton(verify_frame, text="Kiểm tra cú pháp & Tự sửa lỗi sau khi lưu", variable=self.temp_verify_syntax, bootstyle=PRIMARY)
        chk_verify.pack(side=LEFT, padx=(0, 10))
        lbl_verify_attempts = tb.Label(verify_frame, text="Số lần thử sửa:")
        lbl_verify_attempts.pack(side=LEFT, padx=(0, 2))
        self.temp_max_verify_attempts = tk.IntVar(value=self.settings.get("max_verification_attempts", DEFAULT_SETTINGS["max_verification_attempts"]))
        spin_verify_attempts = tb.Spinbox(verify_frame, from_=1, to=20, textvariable=self.temp_max_verify_attempts, width=3)
        spin_verify_attempts.pack(side=LEFT, padx=(0, 5))

        button_frame = tb.Frame(frame, padding=(0, 10, 0, 0))
        button_frame.grid(row=4, column=0, sticky=E, pady=(10, 0))
        btn_apply = tb.Button(button_frame, text="Áp dụng & Lưu", command=self.save_and_apply_settings, bootstyle=PRIMARY)
        btn_apply.pack(side=RIGHT, padx=5)


    def update_api_key_info(self):
        if not hasattr(self, 'lbl_api_info') or not hasattr(self, 'entry_api'): return
        using_env_key = API_KEY_FROM_ENV and self.gemini_api_key == API_KEY_FROM_ENV
        has_saved_key = self.settings.get("gemini_api_key") and not using_env_key
        if using_env_key:
            self.lbl_api_info.config(text="Key lấy từ biến môi trường (GEMINI_API_KEY). Không thể sửa.", bootstyle=INFO)
            self.entry_api.config(state=DISABLED); self.temp_api_key.set("")
        else:
            self.entry_api.config(state=NORMAL); self.temp_api_key.set(self.gemini_api_key)
            txt = "Dùng API key từ Google AI Studio." if has_saved_key else "Nhập Gemini API Key. Lấy từ Google AI Studio."
            self.lbl_api_info.config(text=txt, bootstyle=DEFAULT)

    def save_and_apply_settings(self):
        required_temp_vars = [
            'temp_window_size', 'temp_batch_size', 'temp_rpm_limit',
            'temp_batch_retries', 'temp_item_retries', 'temp_retry_delay',
            'temp_api_key', 'temp_theme', 'temp_font_family', 'temp_font_size',
            'temp_string_mode', 'temp_verify_syntax', 'temp_max_verify_attempts',
            'temp_use_gemini_scan'
        ]
        all_vars_exist = True; missing_vars = []
        for var_name in required_temp_vars:
            if not hasattr(self, var_name): all_vars_exist = False; missing_vars.append(var_name)
        if not all_vars_exist:
             err_msg = f"Lỗi nội bộ: Biến tạm thời thiếu: {', '.join(missing_vars)}"; print(err_msg)
             Messagebox.show_error(err_msg + "\nVui lòng khởi động lại.", "Lỗi Lưu Cài đặt", parent=self); return

        try:
            size_str = self.temp_window_size.get()
            if not re.fullmatch(r"\d{3,}x\d{3,}", size_str):
                Messagebox.show_warning(f"Định dạng kích thước không hợp lệ: '{size_str}'.", "Lỗi Định dạng", parent=self); return
            batch_size = self.temp_batch_size.get(); rpm_limit = self.temp_rpm_limit.get()
            batch_retries = self.temp_batch_retries.get(); item_retries = self.temp_item_retries.get()
            retry_delay = self.temp_retry_delay.get(); api_key_to_save = self.temp_api_key.get()
            font_size = self.temp_font_size.get(); theme = self.temp_theme.get()
            font_family = self.temp_font_family.get()
            string_mode = self.temp_string_mode.get()
            verify_syntax = self.temp_verify_syntax.get()
            max_verify_attempts = self.temp_max_verify_attempts.get()
            use_gemini_scan = self.temp_use_gemini_scan.get()

            if batch_size < 1 or rpm_limit < 1 or batch_retries < 0 or item_retries < 0 or retry_delay < 1 or max_verify_attempts < 1:
                 Messagebox.show_warning("Giá trị cài đặt số không hợp lệ (phải >= 0 hoặc >= 1).", "Lỗi Cài đặt", parent=self); return
            if string_mode not in ["none", "safe_ast", "all"]:
                 Messagebox.show_warning(f"Chế độ dịch chuỗi không hợp lệ: '{string_mode}'.", "Lỗi Cài đặt", parent=self); return

        except tk.TclError as e:
             Messagebox.show_error(f"Lỗi đọc giá trị cài đặt: {e}", "Lỗi Đọc Cài đặt", parent=self); return
        except Exception as e:
             Messagebox.show_error(f"Lỗi không xác định khi đọc cài đặt: {e}", "Lỗi Nghiêm trọng", parent=self); return

        new_settings = {
            "theme": theme, "font_family": font_family, "font_size": font_size,
            "window_size": size_str, "gemini_api_key": api_key_to_save,
            "target_languages": self.settings.get("target_languages", DEFAULT_SETTINGS["target_languages"]),
            "default_target_lang": self.settings.get("default_target_lang", DEFAULT_SETTINGS["default_target_lang"]),
            "batch_size": batch_size, "rpm_limit": rpm_limit,
            "max_batch_retries": batch_retries, "max_item_retries": item_retries,
            "retry_delay_seconds": retry_delay,
            "string_translation_mode": string_mode,
            "verify_syntax_after_save": verify_syntax,
            "max_verification_attempts": max_verify_attempts,
            "use_gemini_scan": use_gemini_scan
        }
        self.apply_settings(new_settings)

    def apply_settings(self, new_settings):
        old_api_key = self.gemini_api_key; old_theme = self.current_theme; old_string_mode = self.settings.get("string_translation_mode")
        old_verify = self.settings.get("verify_syntax_after_save"); old_max_verify = self.settings.get("max_verification_attempts")
        old_font_family = self.settings.get("font_family"); old_font_size = self.settings.get("font_size")
        old_use_gemini = self.settings.get("use_gemini_scan")

        self.settings.update(new_settings)

        new_theme = self.settings.get("theme");
        if new_theme != old_theme:
             try: self.style.theme_use(new_theme); self.current_theme = new_theme; self.update_treeview_tags()
             except Exception as e: print(f"Theme apply error: {e}"); self.settings["theme"] = old_theme

        new_size = self.settings.get("window_size");
        try:
             if self.winfo_exists() and self.geometry() != new_size: self.geometry(new_size)
        except Exception as e: print(f"Size apply error: {e}"); self.settings["window_size"] = self.geometry()

        new_ff = self.settings.get("font_family"); new_fs = self.settings.get("font_size");
        if new_ff != old_font_family or new_fs != old_font_size: self.update_global_font()

        key_from_set = self.settings.get("gemini_api_key", ""); effective_key = key_from_set or API_KEY_FROM_ENV or ""
        key_changed = effective_key != old_api_key; self.gemini_api_key = effective_key
        if key_changed: print("API Key changed."); self.configure_gemini()

        self.batch_size = max(1, int(self.settings.get("batch_size")))
        self.rpm_limit = max(1, int(self.settings.get("rpm_limit")))
        self.seconds_per_request = 60.0 / self.rpm_limit if self.rpm_limit > 0 else 0

        global MAX_BATCH_RETRIES, MAX_ITEM_RETRIES, RETRY_DELAY_SECONDS, VERIFY_SYNTAX, MAX_VERIFICATION_ATTEMPTS
        MAX_BATCH_RETRIES = max(0, int(self.settings.get("max_batch_retries")))
        MAX_ITEM_RETRIES = max(0, int(self.settings.get("max_item_retries")))
        RETRY_DELAY_SECONDS = max(1, int(self.settings.get("retry_delay_seconds")))
        VERIFY_SYNTAX = bool(self.settings.get("verify_syntax_after_save"))
        MAX_VERIFICATION_ATTEMPTS = max(1, int(self.settings.get("max_verification_attempts")))

        new_string_mode = self.settings.get("string_translation_mode")
        if new_string_mode != old_string_mode:
            print(f"String translation mode changed to: {new_string_mode}")
            if hasattr(self, 'string_translation_mode_var'): self.string_translation_mode_var.set(new_string_mode)

        new_verify_mode = self.settings.get("verify_syntax_after_save")
        if new_verify_mode != old_verify:
             print(f"Syntax verification changed to: {new_verify_mode}")
             if hasattr(self, 'verify_syntax_var'): self.verify_syntax_var.set(new_verify_mode)

        new_use_gemini = self.settings.get("use_gemini_scan")
        if new_use_gemini != old_use_gemini:
            print(f"Gemini smart scan mode changed to: {new_use_gemini}")
            if hasattr(self, 'use_gemini_scan_var'): self.use_gemini_scan_var.set(new_use_gemini)

        self.save_settings()

        if hasattr(self, 'temp_theme'): self.temp_theme.set(self.settings['theme'])
        if hasattr(self, 'temp_font_family'): self.temp_font_family.set(self.settings['font_family'])
        if hasattr(self, 'temp_font_size'): self.temp_font_size.set(self.settings['font_size'])
        if hasattr(self, 'temp_window_size'): self.temp_window_size.set(self.settings['window_size'])
        if hasattr(self, 'temp_batch_size'): self.temp_batch_size.set(self.settings['batch_size'])
        if hasattr(self, 'temp_rpm_limit'): self.temp_rpm_limit.set(self.settings['rpm_limit'])
        if hasattr(self, 'temp_batch_retries'): self.temp_batch_retries.set(self.settings['max_batch_retries'])
        if hasattr(self, 'temp_item_retries'): self.temp_item_retries.set(self.settings['max_item_retries'])
        if hasattr(self, 'temp_retry_delay'): self.temp_retry_delay.set(self.settings['retry_delay_seconds'])
        if hasattr(self, 'temp_string_mode'): self.temp_string_mode.set(self.settings['string_translation_mode'])
        if hasattr(self, 'temp_verify_syntax'): self.temp_verify_syntax.set(self.settings['verify_syntax_after_save'])
        if hasattr(self, 'temp_max_verify_attempts'): self.temp_max_verify_attempts.set(self.settings['max_verification_attempts'])
        if hasattr(self, 'temp_use_gemini_scan'): self.temp_use_gemini_scan.set(self.settings['use_gemini_scan'])

        self.update_api_key_info()
        if hasattr(self, 'status_bar'): self.status_bar.config(text="Đã cập nhật và lưu cài đặt.")

    def update_treeview_tags(self):
        if not hasattr(self, 'style') or not hasattr(self.style, 'colors'): return
        colors = self.style.colors
        try:
            tags = {'pending': colors.info, 'processing': colors.primary, 'done': colors.success,
                    'error': colors.danger, 'skipped': colors.secondary, 'empty': colors.secondary,
                    'retry_error': colors.warning, 'reverted': colors.dark,
                    'checked': colors.success, 'unchecked': colors.secondary,
                    'suspicious': colors.danger }
            for tag, color in tags.items():
                if hasattr(self, 'tree_trans') and self.tree_trans:
                    try: self.tree_trans.tag_configure(tag, foreground=color)
                    except tk.TclError: pass
                if hasattr(self, 'tree_comments') and self.tree_comments:
                     if tag in ['checked', 'unchecked']:
                         try: self.tree_comments.tag_configure(tag, foreground=color)
                         except tk.TclError: pass

            base_bg = self.style.lookup('Treeview', 'background'); base_fg = self.style.lookup('Treeview', 'foreground')
            family = self.settings.get("font_family"); size = self.settings.get("font_size")
            current_app_font = tkfont.Font(family=family, size=size)
            linespace = current_app_font.metrics('linespace'); dynamic_row_height = linespace + 4
            self.style.configure('Treeview', background=base_bg, foreground=base_fg, font=current_app_font, rowheight=dynamic_row_height)
            self.style.configure('Treeview.Heading', font=(family, size, 'bold'))
            if hasattr(self, 'tree_trans'): self.tree_trans.configure(style='Treeview')
            if hasattr(self, 'tree_comments'): self.tree_comments.configure(style='Treeview')
        except Exception as e: print(f"Warn: Tag/style config error: {e}")

    def show_translation_view(self):
        if hasattr(self, 'comment_result_frame'): self.comment_result_frame.grid_remove()
        if hasattr(self, 'trans_result_frame'): self.trans_result_frame.grid()
    def show_comments_view(self):
        if hasattr(self, 'trans_result_frame'): self.trans_result_frame.grid_remove()
        if hasattr(self, 'comment_result_frame'): self.comment_result_frame.grid()

    def select_file(self):
        self.hide_initial_help()
        file_path = filedialog.askopenfilename(title="Chọn file Python", filetypes=[("Python files", "*.py"), ("All files", "*.*")])
        if file_path:
            self.source_file_path.set(file_path); self.update_status(f"Đã chọn: {Path(file_path).name}")
            self.reset_ui_for_new_file()

    def reset_ui_for_new_file(self):
        self.scan_complete = False
        self.scan_produced_strings = False
        self.is_translating = False; self.is_paused = False; self.stop_flag = False
        self.btn_translate.config(state=NORMAL, text="Quét / Dịch")
        self.btn_pause_resume.config(state=DISABLED, text="Tạm dừng"); self.btn_stop.config(state=DISABLED)
        self.btn_save_trans.config(state=DISABLED)
        self.btn_run_test.config(state=DISABLED)

        self.btn_scan_comments.config(state=NORMAL)
        self.btn_check_all_comments.config(state=DISABLED)
        self.btn_uncheck_all_comments.config(state=DISABLED)
        self.btn_save_comments.config(state=DISABLED)

        if hasattr(self, 'chk_auto_exclude_comments'):
            self.chk_auto_exclude_comments.config(state=DISABLED)
        if hasattr(self, 'auto_exclude_comments_var'):
            self.auto_exclude_comments_var.set(False)


        if hasattr(self, 'btn_select_all_trans'):
            self.btn_select_all_trans.config(state=DISABLED)
        if hasattr(self, 'btn_deselect_all_trans'):
            self.btn_deselect_all_trans.config(state=DISABLED)

        self.ids_excluded_by_comment_filter.clear()

        self.clear_translation_results(); self.clear_comment_results()
        if hasattr(self, 'trans_result_frame'): self.trans_result_frame.grid_remove()
        if hasattr(self, 'comment_result_frame'): self.comment_result_frame.grid_remove()
        self.detected_source_lang.set("N/A")
        self.update_status("Sẵn sàng quét hoặc chọn file.")

    def clear_translation_results(self):
        if hasattr(self, 'tree_trans'):
            for item in self.tree_trans.get_children(): self.tree_trans.delete(item)
        self.translation_data = []
        self.scan_produced_strings = False
        if hasattr(self, 'btn_save_trans'): self.btn_save_trans.config(state=DISABLED)

        if hasattr(self, 'chk_auto_exclude_comments'):
            self.chk_auto_exclude_comments.config(state=DISABLED)
        if hasattr(self, 'auto_exclude_comments_var'):
            self.auto_exclude_comments_var.set(False)


        if hasattr(self, 'btn_select_all_trans'):
            self.btn_select_all_trans.config(state=DISABLED)
        if hasattr(self, 'btn_deselect_all_trans'):
            self.btn_deselect_all_trans.config(state=DISABLED)

        self.ids_excluded_by_comment_filter.clear()

    def clear_comment_results(self):
        if hasattr(self, 'tree_comments'):
            for item in self.tree_comments.get_children(): self.tree_comments.delete(item)
        self.comment_data = []
        if hasattr(self, 'btn_check_all_comments'): self.btn_check_all_comments.config(state=DISABLED)
        if hasattr(self, 'btn_uncheck_all_comments'): self.btn_uncheck_all_comments.config(state=DISABLED)
        if hasattr(self, 'btn_save_comments'): self.btn_save_comments.config(state=DISABLED)


    def update_status(self, message):
        if hasattr(self, 'status_bar'):
            self.status_bar.config(text=f"Trạng thái: {message}")
            self.update_idletasks()

    def toggle_pause(self):
        if self.is_translating:
            self.is_paused = not self.is_paused;
            can_save = bool(self.source_file_path.get() and self.translation_data and not self.is_translating)
            if hasattr(self, 'btn_save_trans'): self.btn_save_trans.config(state=NORMAL if can_save else DISABLED)
            pause_state = NORMAL if self.is_translating else DISABLED
            self.btn_pause_resume.config(text="Tiếp tục" if self.is_paused else "Tạm dừng", state=pause_state)
            self.update_status("Đã tạm dừng dịch..." if self.is_paused else "Đang tiếp tục dịch...")

    def stop_translation(self):
         if self.is_translating:
            self.stop_flag = True
            if self.is_paused: self.is_paused = False; self.btn_pause_resume.config(text="Tạm dừng", state=DISABLED)
            self.update_status("Đang dừng quá trình dịch..."); self.btn_stop.config(state=DISABLED)

    def scan_comments(self):
        self.hide_initial_help()
        if not self.source_file_path.get(): Messagebox.show_warning("Chưa chọn file Python.", "Lỗi", parent=self); return
        self.reset_ui_for_new_action()
        self.clear_comment_results(); self.show_comments_view(); self.update_status("Đang quét comments...")
        self.btn_scan_comments.config(state=DISABLED)
        self.btn_check_all_comments.config(state=DISABLED)
        self.btn_uncheck_all_comments.config(state=DISABLED)
        self.btn_save_comments.config(state=DISABLED)
        self.btn_translate.config(state=DISABLED)

        thread = threading.Thread(target=self._scan_comments_thread, daemon=True); thread.start()

    def reset_ui_for_new_action(self):
         self.scan_complete = False
         self.scan_produced_strings = False
         self.is_translating = False; self.is_paused = False; self.stop_flag = False
         if hasattr(self, 'btn_translate'): self.btn_translate.config(text="Quét / Dịch", state=NORMAL if self.source_file_path.get() else DISABLED)
         if hasattr(self, 'btn_pause_resume'): self.btn_pause_resume.config(state=DISABLED, text="Tạm dừng")
         if hasattr(self, 'btn_stop'): self.btn_stop.config(state=DISABLED)
         if hasattr(self, 'btn_run_test'): self.btn_run_test.config(state=DISABLED)

         if hasattr(self, 'btn_check_all_comments'): self.btn_check_all_comments.config(state=DISABLED)
         if hasattr(self, 'btn_uncheck_all_comments'): self.btn_uncheck_all_comments.config(state=DISABLED)
         if hasattr(self, 'btn_save_comments'): self.btn_save_comments.config(state=DISABLED)

         if hasattr(self, 'chk_auto_exclude_comments'):
             self.chk_auto_exclude_comments.config(state=DISABLED)
         if hasattr(self, 'auto_exclude_comments_var'):
             self.auto_exclude_comments_var.set(False)

         if hasattr(self, 'btn_select_all_trans'):
             self.btn_select_all_trans.config(state=DISABLED)
         if hasattr(self, 'btn_deselect_all_trans'):
             self.btn_deselect_all_trans.config(state=DISABLED)

         self.ids_excluded_by_comment_filter.clear()


    def _scan_comments_thread(self):
        try:
            filepath = self.source_file_path.get(); comments = self.extract_comments(filepath)
            if not comments:
                self.after(0, self.update_status, "Không tìm thấy comments.")
                self.after(0, self.btn_scan_comments.config, {"state": NORMAL})
                self.after(0, self.btn_translate.config, {"state": NORMAL})
                return

            self.after(0, self.populate_comments_treeview, comments)
            self.after(0, self.update_status, f"Đã tìm thấy {len(comments)} comments.")
            self.after(0, self.btn_scan_comments.config, {"state": NORMAL})
            self.after(0, self.btn_translate.config, {"state": NORMAL})
            self.after(0, self.btn_check_all_comments.config, {"state": NORMAL})
            self.after(0, self.btn_uncheck_all_comments.config, {"state": NORMAL})
            self.after(0, self.btn_save_comments.config, {"state": NORMAL})

        except FileNotFoundError:
            self.after(0, self.update_status, "Lỗi: Không tìm thấy file khi quét comments.")
            self.after(0, self.btn_scan_comments.config, {"state": NORMAL})
            self.after(0, self.btn_translate.config, {"state": NORMAL})
        except tokenize.TokenError as e:
            self.after(0, self.update_status, f"Lỗi phân tích comments: {e}")
            self.after(0, self.btn_scan_comments.config, {"state": NORMAL})
            self.after(0, self.btn_translate.config, {"state": NORMAL})
        except Exception as e:
            print(f"Error scanning comments: {e}"); traceback.print_exc()
            self.after(0, self.update_status, f"Lỗi quét comments: {e}")
            self.after(0, self.btn_scan_comments.config, {"state": NORMAL})
            self.after(0, self.btn_translate.config, {"state": NORMAL})

    def extract_comments(self, filepath):
        comments = []
        try:
            with open(filepath, 'rb') as fb: file_content_bytes = fb.read()
            buffer = io.BytesIO(file_content_bytes)
            tokens = tokenize.tokenize(buffer.readline)
            for t in tokens:
                if t.type == tokenize.COMMENT: comments.append((t, t.string))
        except tokenize.TokenError as e: print(f"Token Error extracting comments: {e}"); raise
        except FileNotFoundError: print(f"File Not Found extracting comments: {filepath}"); raise
        except Exception as e: print(f"General Error extracting comments: {e}"); traceback.print_exc(); raise
        return comments

    def populate_comments_treeview(self, comments):
        self.clear_comment_results(); self.comment_data = []; last_id = None
        edit_icon = "✒️"
        for token_info, original_text in comments:
            line = token_info.start[0]
            keep_var = tk.BooleanVar(value=True)
            cb_display = "☑" if keep_var.get() else "☐"
            try:
                item_id = self.tree_comments.insert("", END, values=(line, original_text.strip(), edit_icon, cb_display))
                last_id = item_id; self.tree_comments.item(item_id, tags=("checked",))
                self.comment_data.append([token_info, original_text, keep_var, item_id])
                keep_var.trace_add("write", lambda *a, i=len(self.comment_data)-1: self.update_comment_checkbox_display(i))
            except tk.TclError as e: print(f"Comment tree insert error: {e}")
        if last_id and hasattr(self, 'tree_comments') and self.tree_comments.exists(last_id): self.tree_comments.see(last_id)


    def update_comment_checkbox_display(self, index):
        if index < len(self.comment_data):
            _, _, keep_var, item_id = self.comment_data[index]
            if hasattr(self, 'tree_comments') and self.tree_comments.exists(item_id):
                is_checked = keep_var.get(); cb = "☑" if is_checked else "☐"
                try:
                    vals = list(self.tree_comments.item(item_id, 'values'))
                    if len(vals) >= 4:
                        vals[3] = cb
                        self.tree_comments.item(item_id, values=tuple(vals), tags=("checked" if is_checked else "unchecked",))
                except tk.TclError as e: print(f"TclError updating comment display: {e}")
                except IndexError as e_idx: print(f"IndexError updating comment display {item_id}: {e_idx}")


    def handle_comment_single_click(self, event):
        """Handles single clicks on the comment tree, specifically for the edit column."""
        if not hasattr(self, 'tree_comments'): return
        region = self.tree_comments.identify_region(event.x, event.y)
        if region != "cell": return

        column_id = self.tree_comments.identify_column(event.x)
        item_id = self.tree_comments.identify_row(event.y)

        if not item_id: return

        if column_id == "#3":
            self.edit_comment_content(item_id)


    def edit_comment_content(self, item_id):
        """Opens a dialog to edit the content of the selected comment."""
        target_index = -1
        for i, data in enumerate(self.comment_data):
            if len(data) >= 4 and data[3] == item_id:
                target_index = i
                break

        if target_index == -1:
            print(f"Error: Could not find comment data for item_id {item_id}")
            return

        token_info, original_full_comment, keep_var, _ = self.comment_data[target_index]

        prefix_match = re.match(r'^(\s*#+\s*)', original_full_comment)
        prefix = prefix_match.group(1) if prefix_match else "# "
        current_text = original_full_comment[len(prefix):]

        new_text = simpledialog.askstring(
            "Edit Comment",
            f"Sửa nội dung comment (Dòng {token_info.start[0]}):",
            initialvalue=current_text,
            parent=self
        )

        if new_text is not None:
            new_text = new_text.strip()
            new_full_comment = prefix + new_text

            self.comment_data[target_index][1] = new_full_comment

            try:
                if hasattr(self, 'tree_comments') and self.tree_comments.exists(item_id):
                    current_values = list(self.tree_comments.item(item_id, 'values'))
                    if len(current_values) >= 2:
                        current_values[1] = new_full_comment.strip()
                        self.tree_comments.item(item_id, values=tuple(current_values))
                        self.update_status(f"Đã sửa comment dòng {token_info.start[0]}.")
            except tk.TclError as e:
                print(f"Error updating comment tree after edit: {e}")
            except IndexError as e_idx:
                print(f"IndexError updating comment tree after edit {item_id}: {e_idx}")


    def handle_comment_double_click(self, event):
        """Handles double-clicks on the comment tree for toggling the keep checkbox."""
        if not hasattr(self, 'tree_comments'): return

        item_id = self.tree_comments.identify_row(event.y)
        if not item_id: return

        column_id = self.tree_comments.identify_column(event.x)
        if column_id == "#3":
            return

        for data in self.comment_data:
            if len(data) >= 4 and data[3] == item_id:
                data[2].set(not data[2].get())
                break



    def select_all_comments(self):
        """Sets all comment checkboxes to True (checked/keep)."""
        if not self.comment_data: return
        updated = 0
        for d in self.comment_data:
            if len(d) >= 3 and not d[2].get():
                d[2].set(True)
                updated += 1
        if updated > 0:
            self.update_status(f"Đã Check ALL ({updated} comments).")
        else:
            self.update_status("Tất cả comments đã được Check.")

    def deselect_all_comments(self):
        """Sets all comment checkboxes to False (unchecked/remove)."""
        if not self.comment_data: return
        updated = 0
        for d in self.comment_data:
             if len(d) >= 3 and d[2].get():
                d[2].set(False)
                updated += 1
        if updated > 0:
            self.update_status(f"Đã Uncheck ALL ({updated} comments).")
        else:
            self.update_status("Tất cả comments đã được Uncheck.")


    def save_comment_changes(self):
        """Initiates saving the file, keeping only checked comments."""
        if not self.source_file_path.get():
            Messagebox.show_warning("Chưa chọn file.", parent=self)
            return
        if not self.comment_data:
            Messagebox.show_info("Không có comment nào được quét.", parent=self)
            return

        self.save_comments_file(keep_those_marked_true=True)

    def save_comments_file(self, keep_those_marked_true=True):
        """
        Prompts user for save location and starts the save process in a thread.
        The 'keep_those_marked_true' parameter determines the saving behavior:
        - True: (Default and intended use now) Removes comments where the checkbox (keep_var) is False.
        - False: (Legacy, not used by UI anymore) Removes ALL comments.
        """
        orig_path = Path(self.source_file_path.get())
        suffix = "_managed"
        def_name = f"{orig_path.stem}_comments{suffix}{orig_path.suffix}"
        save_path_str = filedialog.asksaveasfilename(
            title="Lưu file Comments đã quản lý",
            initialdir=orig_path.parent,
            initialfile=def_name,
            defaultextension=".py",
            filetypes=[("Python", "*.py"), ("All", "*.*")]
        )
        if not save_path_str:
            self.update_status("Hủy lưu comments.")
            return

        save_path = Path(save_path_str)
        if save_path.resolve() == orig_path.resolve():
            Messagebox.show_error("KHÔNG LƯU! Trùng file gốc.", parent=self)
            return

        self.update_status(f"Đang lưu comments vào: {save_path.name}...")
        threading.Thread(
            target=self._execute_save_comments,
            args=(orig_path, save_path, keep_those_marked_true),
            daemon=True
        ).start()

    def _execute_save_comments(self, original_path, save_path, keep_those_marked_true):
        """Writes the new file content, removing comments based on the flag."""
        try:
            original_lines = []; used_encoding = 'utf-8'
            try:
                with open(original_path, 'r', encoding=used_encoding) as f: original_lines = f.readlines()
            except UnicodeDecodeError:
                try:
                    used_encoding = None;
                    with open(original_path, 'r', encoding=used_encoding) as f: original_lines = f.readlines()
                    self.after(0, self.update_status, "Cảnh báo: Đọc bằng encoding mặc định.")
                except Exception as e_fb: self.after(0, self.update_status, f"Lỗi đọc file gốc: {e_fb}"); return

            output_lines = list(original_lines); lines_to_delete = set(); ranges_to_clear = []; removal_count = 0
            comments_to_process = self.comment_data

            line_modification_data = {}
            comments_to_remove_indices = []

            for index, comment_item in enumerate(comments_to_process):
                 if len(comment_item) < 4: continue
                 token_info, original_or_edited_text, keep_var, item_id = comment_item

                 should_keep = keep_var.get() if keep_those_marked_true else False

                 start_idx = token_info.start[0] - 1
                 start_col, end_col = token_info.start[1], token_info.end[1]
                 if start_idx < 0 or start_idx >= len(original_lines): continue

                 original_line_strip = original_lines[start_idx].strip()

                 try:
                     original_token_text = tokenize.tok_name[token_info.type] + " " + token_info.string
                     original_line_content = original_lines[start_idx]
                     if original_line_strip == token_info.string.strip():
                          is_full_line = True
                     else:
                          is_full_line = False
                 except Exception:
                      is_full_line = original_line_strip.startswith("#")

                 if not should_keep:
                     removal_count += 1
                     if is_full_line:
                         lines_to_delete.add(start_idx)
                     else:
                         eff_end_col = end_col
                         line_len = len(original_lines[start_idx])
                         if end_col > line_len: eff_end_col = line_len
                         if original_lines[start_idx].endswith('\n') and end_col == line_len + 1: pass
                         if 0 <= start_col < eff_end_col <= line_len:
                              if start_idx not in line_modification_data: line_modification_data[start_idx] = []
                              line_modification_data[start_idx].append((start_col, eff_end_col, ""))
                 else:
                     if original_or_edited_text != token_info.string:
                          eff_end_col = end_col
                          line_len = len(original_lines[start_idx])
                          if end_col > line_len: eff_end_col = line_len
                          if original_lines[start_idx].endswith('\n') and end_col == line_len + 1: pass
                          if 0 <= start_col < eff_end_col <= line_len:
                               if start_idx not in line_modification_data: line_modification_data[start_idx] = []
                               line_modification_data[start_idx].append((start_col, eff_end_col, original_or_edited_text))


            modified_output_lines = list(original_lines)
            for line_idx in sorted(line_modification_data.keys()):
                if line_idx in lines_to_delete: continue

                modifications = line_modification_data[line_idx]
                modifications.sort(key=lambda x: x[0], reverse=True)

                current_line_content = modified_output_lines[line_idx]
                for start_col, end_col, replacement in modifications:
                    if 0 <= start_col <= end_col <= len(current_line_content):
                        current_line_content = current_line_content[:start_col] + replacement + current_line_content[end_col:]
                    else:
                         print(f"Warning: Skipping modification on line {line_idx+1} due to index mismatch after previous edits.")

                original_line_stripped = original_lines[line_idx].strip()
                if original_line_stripped:
                    modified_output_lines[line_idx] = current_line_content.rstrip()
                    if original_lines[line_idx].endswith('\n') and not modified_output_lines[line_idx].endswith('\n'):
                         modified_output_lines[line_idx] += '\n'
                else:
                    modified_output_lines[line_idx] = current_line_content


            final_lines = []
            for i, line in enumerate(modified_output_lines):
                 if i not in lines_to_delete:
                     orig_is_ws = original_lines[i].strip() == ""
                     curr_is_ws = line.strip() == ""
                     if not curr_is_ws or orig_is_ws:
                          final_lines.append(line)

            self.after(0, self.update_status, f"Đang ghi vào: {save_path.name}...")
            with open(save_path, 'w', encoding='utf-8') as f: f.writelines(final_lines)

            mode_desc = "đã xóa các comment không được chọn (☐)"
            kept_count = len(comments_to_process) - removal_count
            msg = f"Đã lưu file ({kept_count} comment được giữ ☑, {removal_count} comment bị xóa ☐) vào: {save_path}"
            self.after(0, self.update_status, msg)
            self.after(0, lambda: Messagebox.show_info(f"Lưu quản lý comments thành công!\n({kept_count} comment được giữ, {removal_count} comment bị xóa)\n\n{save_path}", "Lưu thành công", parent=self))
        except Exception as e:
             print(f"Error saving comments file: {e}"); traceback.print_exc()
             self.after(0, self.update_status, f"Lỗi lưu comments: {e}")


    def handle_scan_or_translate(self):
        self.hide_initial_help()
        if not self.source_file_path.get():
            Messagebox.show_warning("Chưa chọn file.", parent=self)
            return

        if not self.scan_complete:
            self.clear_translation_results()
            self.show_translation_view()
            self.update_status("Bắt đầu quét...")
            self.btn_translate.config(state=DISABLED)
            self.btn_scan_comments.config(state=DISABLED)
            self.btn_save_trans.config(state=DISABLED)
            self.btn_pause_resume.config(state=DISABLED)
            self.btn_stop.config(state=DISABLED)
            self.btn_run_test.config(state=DISABLED)
            if hasattr(self, 'chk_auto_exclude_comments'):
                self.chk_auto_exclude_comments.config(state=DISABLED)
            if hasattr(self, 'btn_select_all_trans'):
                self.btn_select_all_trans.config(state=DISABLED)
            if hasattr(self, 'btn_deselect_all_trans'):
                self.btn_deselect_all_trans.config(state=DISABLED)

            thread = threading.Thread(target=self._scan_file_thread, daemon=True)
            thread.start()
        else:
            self.start_actual_translation()

    def _call_gemini_for_line_identification(self, code_content: str) -> tuple[str | None, str | None]:
        """
        Calls Gemini to identify lines containing potentially translatable text.
        Returns tuple (response_text | None, error_message | None)
        """
        if not self.gemini_model:
            if not self.configure_gemini(): return None, "Lỗi cấu hình lại Gemini"
            if not self.gemini_model: return None, "Không thể khởi tạo Gemini"
        if not code_content.strip():
            return "", None

        prompt = (
            "Analyze the following Python code. Identify all lines that contain natural language text "
            "(in comments or string literals) which is likely intended for translation (e.g., user interface text, "
            "error messages shown to users, descriptive comments explaining logic). "
            "Exclude lines containing only code identifiers, file paths, URLs, SQL queries, configuration keys, "
            "regular expressions, format specifiers, HTML/XML tags, or technical terms/constants not meant for translation.\n\n"
            "Your response MUST be a single line string containing only the identified line numbers, "
            "followed by the count of distinct translatable segments found on that line in parentheses. "
            "Separate each entry with a semicolon (;).\n"
            "Example: If line 5 has one translatable string and line 12 has two (a comment and a string), "
            "the output should be exactly: 5(1);12(2)\n"
            "If no translatable lines are found, return an empty string.\n"
            "Do NOT include any explanations, introductions, summaries, or markdown formatting. Only the semicolon-separated list.\n\n"
            "Python Code:\n"
            "```python\n"
            f"{code_content}\n"
            "```\n\n"
            "Response:"
        )
        safety_settings = [{"category": c, "threshold": "BLOCK_NONE"} for c in ["HARM_CATEGORY_HARASSMENT", "HARM_CATEGORY_HATE_SPEECH", "HARM_CATEGORY_SEXUALLY_EXPLICIT", "HARM_CATEGORY_DANGEROUS_CONTENT"]]
        generation_config = genai.types.GenerationConfig(temperature=0.1)

        try:
            current_time = time.time(); time_since_last_call = current_time - self.last_api_call_time
            if self.seconds_per_request > 0 and time_since_last_call < self.seconds_per_request:
                 time.sleep(self.seconds_per_request - time_since_last_call)
            self.last_api_call_time = time.time()

            response = self.gemini_model.generate_content(prompt, generation_config=generation_config, safety_settings=safety_settings)
            raw_response_text = None
            if hasattr(response, 'text'): raw_response_text = response.text
            elif response.parts: raw_response_text = "".join(p.text for p in response.parts if hasattr(p, 'text'))

            if raw_response_text is not None:
                 if raw_response_text == "" or re.fullmatch(r"^\d+(\(\d+\))?(;\d+(\(\d+\))?)*$", raw_response_text.strip()):
                     return raw_response_text.strip(), None
                 else:
                     error_msg = f"Lỗi định dạng AI: '{raw_response_text[:100]}...'"
                     print(f"AI line identification returned unexpected format: {raw_response_text}")
                     return None, error_msg
            else:
                block_reason = "Unknown";
                try:
                     if hasattr(response, 'prompt_feedback') and response.prompt_feedback.block_reason:
                         block_reason = f"Blocked ({response.prompt_feedback.block_reason})"
                     elif hasattr(response, 'finish_reason') and getattr(response, 'finish_reason', 1) != 1:
                         block_reason = f"Finish Reason: {getattr(response, 'finish_reason', 'UNKNOWN')}"
                except Exception: pass
                error_msg = f"AI bị chặn/lỗi ({block_reason})"
                print(f"AI line identification call blocked or failed. Reason: {block_reason}.")
                return None, error_msg
        except google_exceptions.ResourceExhausted as e_quota:
             print(f"AI line identification Quota/Rate Limit Error (429): {e_quota}")
             return None, "Lỗi Quota/Rate Limit AI (429)"
        except google_exceptions.InvalidArgument as e_arg:
             print(f"AI line identification Invalid Argument Error: {e_arg}")
             return None, f"Lỗi Invalid Argument AI: {str(e_arg)[:100]}..."
        except google_exceptions.GoogleAPIError as e_google_api:
             print(f"Generic Google API Error during line identification: {e_google_api}")
             return None, f"Lỗi API Google (Line ID): {str(e_google_api)[:100]}..."
        except Exception as e_api:
             print(f"Unhandled API Error during line identification: {e_api}"); traceback.print_exc()
             return None, f"Lỗi AI không xác định (Line ID): {str(e_api)[:100]}..."

    def _parse_gemini_line_response(self, response_text: str | None) -> set[int]:
        """Parses the Gemini line identification response string."""
        identified_lines = set()
        if not response_text:
            return identified_lines
        parts = response_text.strip().split(';')
        for part in parts:
            if not part: continue
            match = re.match(r"^\s*(\d+)", part)
            if match:
                try:
                    line_num = int(match.group(1))
                    if line_num > 0: identified_lines.add(line_num)
                except ValueError:
                    print(f"Warning: Could not parse line number from Gemini response part: '{part}'")
        return identified_lines

    def _scan_file_thread(self):
        filepath = self.source_file_path.get()
        if not filepath:
            self.after(0, self.update_status, "Lỗi: Không có đường dẫn file.")
            self.after(0, self.reset_ui_for_new_action); return

        gemini_scan_enabled = self.use_gemini_scan_var.get()
        gemini_target_lines: set[int] | None = None
        gemini_scan_failed = False
        gemini_error_msg = None
        self.scan_produced_strings = False

        try:
            self.after(0, self.update_status, "Đang đọc nội dung file...")
            try:
                with open(filepath, 'r', encoding='utf-8') as f: code_content = f.read()
            except Exception as e_read:
                self.after(0, self.update_status, f"Lỗi đọc file: {e_read}")
                self.after(0, lambda: Messagebox.show_error(f"Không thể đọc file:\n{e_read}", "Lỗi Đọc File", parent=self))
                self.after(0, self.reset_ui_for_new_action); return

            if gemini_scan_enabled:
                if not self.gemini_api_key:
                     self.after(0, self.update_status, "Lỗi API Key: Chuyển sang AST+Content.")
                     gemini_scan_failed = True
                     gemini_error_msg = "Chưa cấu hình API Key Gemini."
                     self.after(0, lambda: Messagebox.show_warning(f"{gemini_error_msg}\nKhông thể sử dụng Quét thông minh.", "Lỗi API Key", parent=self))
                elif not self.gemini_model:
                     if not self.configure_gemini():
                          self.after(0, self.update_status, "Lỗi cấu hình API: Chuyển sang AST+Content.")
                          gemini_scan_failed = True
                          gemini_error_msg = "Lỗi cấu hình Gemini API."
                          self.after(0, lambda: Messagebox.show_warning(f"{gemini_error_msg}\nKhông thể sử dụng Quét thông minh.", "Lỗi API Config", parent=self))
                     if not self.gemini_model:
                           self.after(0, self.update_status, "Lỗi khởi tạo API: Chuyển sang AST+Content.")
                           gemini_scan_failed = True
                           gemini_error_msg = "Không thể khởi tạo mô hình Gemini."
                           self.after(0, lambda: Messagebox.show_warning(f"{gemini_error_msg}\nKhông thể sử dụng Quét thông minh.", "Lỗi API Init", parent=self))

                if not gemini_scan_failed:
                    self.after(0, self.update_status, "Đang xác định dòng cần dịch bằng AI (Gemini)...")
                    gemini_response_text, gemini_error = self._call_gemini_for_line_identification(code_content)

                    if gemini_error:
                        self.after(0, self.update_status, f"Lỗi AI Scan: {gemini_error}. Chuyển sang AST+Content.")
                        gemini_scan_failed = True
                        gemini_error_msg = f"Quét thông minh (Gemini) thất bại:\n{gemini_error}"
                        self.after(0, lambda: Messagebox.show_warning(f"{gemini_error_msg}\n\nĐang sử dụng chế độ quét thông thường (AST+Content).", "Lỗi AI Scan", parent=self))

                    elif gemini_response_text is not None:
                        gemini_target_lines = self._parse_gemini_line_response(gemini_response_text)
                        if not gemini_target_lines:
                            self.after(0, self.update_status, "AI không xác định được dòng nào. Sử dụng AST+Content.")
                            gemini_target_lines = set()
                            self.after(0, lambda: Messagebox.show_info("Quét thông minh (Gemini) không tìm thấy dòng nào cần dịch.\nKết quả hiển thị dựa trên phân tích AST+Content.", "AI Scan", parent=self))
                        else:
                             self.after(0, self.update_status, f"AI xác định {len(gemini_target_lines)} dòng tiềm năng. Đang quét chi tiết...")
                    else:
                        self.after(0, self.update_status, "Lỗi không xác định từ AI Scan. Chuyển sang AST+Content.")
                        gemini_scan_failed = True
                        gemini_error_msg = "Lỗi không xác định từ Gemini API khi quét dòng."
                        self.after(0, lambda: Messagebox.show_warning(f"{gemini_error_msg}\n\nĐang sử dụng chế độ quét thông thường (AST+Content).", "Lỗi AI Scan", parent=self))


            scan_mode_msg = "AST+Content"
            if gemini_scan_enabled:
                if gemini_scan_failed: scan_mode_msg += " (Fallback từ AI lỗi)"
                elif gemini_target_lines is not None: scan_mode_msg += " (kết hợp AI)"

            self.after(0, self.update_status, f"Đang trích xuất chi tiết bằng {scan_mode_msg}...")
            string_mode = self.string_translation_mode_var.get()
            all_potential_elements, content_filtered_count, _, _ = self.extract_code_elements(filepath, string_mode, None)

            if not all_potential_elements:
                 status_msg = "Không tìm thấy comments hoặc strings hợp lệ nào bằng AST+Content."
                 self.after(0, self.update_status, status_msg)
                 self.after(0, self.reset_ui_for_new_action); return

            primary_elements = []
            suspicious_elements = []
            if gemini_scan_enabled and not gemini_scan_failed and gemini_target_lines is not None:
                 ai_missed_count = 0
                 for element in all_potential_elements:
                     token_info, _ = element
                     if token_info.start[0] in gemini_target_lines:
                         primary_elements.append(element)
                     else:
                         suspicious_elements.append(element)
                         ai_missed_count += 1
                 status_suffix = f"Phân loại: {len(primary_elements)} chính (AI gợi ý)"
                 if suspicious_elements: status_suffix += f", {len(suspicious_elements)} nghi ngờ (AI bỏ qua)"
                 if content_filtered_count > 0: status_suffix += f". ({content_filtered_count} mục bị lọc nội dung)"
                 self.after(0, self.update_status, status_suffix)
            else:
                 primary_elements = all_potential_elements
                 status_suffix = f"tìm thấy {len(primary_elements)} mục."
                 if content_filtered_count > 0: status_suffix += f" ({content_filtered_count} mục bị lọc nội dung)"
                 if gemini_scan_enabled and gemini_scan_failed:
                      self.after(0, self.update_status, f"Quét AST+Content (Fallback) {status_suffix}")
                 elif gemini_scan_enabled and gemini_target_lines is not None and not gemini_target_lines:
                       self.after(0, self.update_status, f"Quét AST+Content (AI không tìm thấy dòng nào) {status_suffix}")
                 else:
                      self.after(0, self.update_status, f"Quét AST+Content {status_suffix}")


            if not primary_elements and not suspicious_elements:
                 self.after(0, self.update_status, "Không có mục nào phù hợp sau khi lọc và phân loại.")
                 self.after(0, lambda: self.btn_translate.config(text="Quét / Dịch", state=NORMAL))
                 self.after(0, lambda: self.btn_scan_comments.config(state=NORMAL))
                 return

            self.after(0, self.update_status, "Đang chuẩn bị hiển thị...")
            items_added, has_comments_added, has_strings_added = self.populate_translation_treeview_initial(primary_elements, suspicious_elements)
            self.scan_produced_strings = has_strings_added

            if items_added > 0:
                 final_status_msg = f"Quét xong {items_added} mục. "
                 if suspicious_elements:
                      final_status_msg += f"({len(suspicious_elements)} mục nghi ngờ màu đỏ). "
                 final_status_msg += "Chọn mục cần dịch rồi bấm 'Dịch'."
                 self.after(0, self.update_status, final_status_msg)

                 if hasattr(self, 'chk_auto_exclude_comments'):
                     self.chk_auto_exclude_comments.config(state=NORMAL if has_comments_added else DISABLED)

                 if hasattr(self, 'btn_select_all_trans'):
                     self.btn_select_all_trans.config(state=NORMAL)
                 if hasattr(self, 'btn_deselect_all_trans'):
                     self.btn_deselect_all_trans.config(state=NORMAL)

                 self.after(0, lambda: self.btn_translate.config(text="Dịch", state=NORMAL))
                 self.after(0, lambda: self.btn_save_trans.config(state=NORMAL))
                 self.after(0, lambda: self.btn_run_test.config(state=NORMAL))
                 self.after(0, lambda: self.btn_scan_comments.config(state=NORMAL))
                 self.scan_complete = True
            else:
                 self.after(0, self.update_status, "Quét xong nhưng không có mục hợp lệ nào được thêm vào danh sách.")
                 self.after(0, self.reset_ui_for_new_action)


        except FileNotFoundError:
             self.after(0, self.update_status, f"Lỗi: Không tìm thấy file {self.source_file_path.get()}");
             self.after(0, lambda: Messagebox.show_error(f"Không tìm thấy file:\n{self.source_file_path.get()}", "Lỗi File", parent=self))
             self.after(0, self.reset_ui_for_new_action)
        except (tokenize.TokenError, SyntaxError) as e_parse:
             err_type = "Lỗi phân tích file" if isinstance(e_parse, tokenize.TokenError) else "Lỗi cú pháp file"
             self.after(0, self.update_status, f"{err_type}: {e_parse}");
             self.after(0, lambda: Messagebox.show_error(f"{err_type}:\n{e_parse}\nFile có thể chứa lỗi cú pháp.", err_type, parent=self))
             self.after(0, self.reset_ui_for_new_action)
        except Exception as e_general:
             print(f"Lỗi không xác định khi quét file (Hybrid Flow): {e_general}"); traceback.print_exc();
             self.after(0, self.update_status, f"Lỗi quét không xác định: {e_general}");
             self.after(0, lambda: Messagebox.show_error(f"Đã xảy ra lỗi không mong muốn khi quét:\n{e_general}", "Lỗi Nghiêm trọng", parent=self))
             self.after(0, self.reset_ui_for_new_action)


    def start_actual_translation(self):
        if not self.scan_complete:
             Messagebox.show_info("Vui lòng quét file trước khi dịch.", parent=self); return
        if not self.translation_data:
             Messagebox.show_info("Không có mục nào trong danh sách để dịch.", parent=self); return
        if sum(1 for item in self.translation_data if len(item) >= 6 and not item[5]) == 0:
             Messagebox.show_info("Không có mục nào được chọn (☑) để dịch.", parent=self); return

        if not self.gemini_model:
            if not self.gemini_api_key: Messagebox.show_error("Chưa cấu hình API Key.", parent=self); return
            if not self.configure_gemini(): return
            if not self.gemini_model: Messagebox.show_error("Không thể khởi tạo Gemini.", parent=self); return

        self.update_status("Bắt đầu dịch các mục đã chọn...")
        self.is_translating = True; self.is_paused = False; self.stop_flag = False
        self.btn_translate.config(state=DISABLED); self.btn_scan_comments.config(state=DISABLED)
        self.btn_pause_resume.config(state=NORMAL, text="Tạm dừng"); self.btn_stop.config(state=NORMAL)
        self.btn_save_trans.config(state=DISABLED)
        self.btn_run_test.config(state=DISABLED)
        if hasattr(self, 'chk_auto_exclude_comments'):
             self.chk_auto_exclude_comments.config(state=DISABLED)
        if hasattr(self, 'btn_select_all_trans'):
            self.btn_select_all_trans.config(state=DISABLED)
        if hasattr(self, 'btn_deselect_all_trans'):
            self.btn_deselect_all_trans.config(state=DISABLED)

        thread = threading.Thread(target=self.process_file_translation_only, daemon=True)
        thread.start()


    def _call_gemini_api(self, texts_to_translate: list[str], target_language: str) -> tuple[list[str] | None, str | None]:
        if not self.gemini_model:
            if not self.configure_gemini(): return None, "Lỗi cấu hình lại Gemini"
            if not self.gemini_model: return None, "Không thể khởi tạo Gemini"
        if not texts_to_translate: return [], None

        separator = " ||| TRANSLATION_UNIT ||| "; joined_text = separator.join(texts_to_translate); n_items = len(texts_to_translate)
        prompt = (f"Translate the following {n_items} text snippet(s) delimited by '{separator}' into {target_language}. "
                  f"IMPORTANT: Your response MUST contain ONLY the translated snippets, in the exact same order, "
                  f"delimited by the exact separator string '{separator}'. "
                  f"DO NOT start the response with the separator '{separator}'. "
                  f"DO NOT include ANY introductory text, concluding text, explanations, numbering, markdown formatting, "
                  f"or anything else outside the translated snippets and the separators. "
                  f"Preserve technical terms or code variables within the text where appropriate. "
                  f"If a snippet is technical (like code, path, constant) or meaningless (like '---', '...') and should not be translated, return it unchanged. "
                  f"Example input (2 items): snippet1{separator}snippet2\n"
                  f"Example expected output (2 items): translated_snippet1{separator}translated_snippet2\n"
                  f"Example input (1 item): snippet1\n"
                  f"Example expected output (1 item): translated_snippet1\n\n"
                  f"Input:\n{joined_text}")
        safety_settings = [{"category": c, "threshold": "BLOCK_NONE"} for c in ["HARM_CATEGORY_HARASSMENT", "HARM_CATEGORY_HATE_SPEECH", "HARM_CATEGORY_SEXUALLY_EXPLICIT", "HARM_CATEGORY_DANGEROUS_CONTENT"]]
        generation_config = genai.types.GenerationConfig(temperature=0.2)
        try:
            current_time = time.time(); time_since_last_call = current_time - self.last_api_call_time
            if self.seconds_per_request > 0 and time_since_last_call < self.seconds_per_request:
                 time.sleep(self.seconds_per_request - time_since_last_call)
            self.last_api_call_time = time.time()

            response = self.gemini_model.generate_content(prompt, generation_config=generation_config, safety_settings=safety_settings)
            raw_response_text = "N/A"
            if hasattr(response, 'text'): raw_response_text = response.text
            elif response.parts: raw_response_text = "".join(p.text for p in response.parts if hasattr(p, 'text'))
            else:
                 block_reason = "Unknown";
                 try:
                     if hasattr(response, 'prompt_feedback') and response.prompt_feedback.block_reason:
                         block_reason = f"Blocked ({response.prompt_feedback.block_reason})"
                     elif hasattr(response, 'finish_reason') and getattr(response, 'finish_reason', 1) != 1:
                         block_reason = f"Finish Reason: {getattr(response, 'finish_reason', 'UNKNOWN')}"
                 except Exception: pass
                 error_msg = f"API bị chặn/lỗi ({block_reason})"
                 print(f"API call blocked or failed. Reason: {block_reason}. Input ({n_items}, first 2): {texts_to_translate[:2]}...")
                 return None, error_msg

            translated_joined = raw_response_text.strip()
            if translated_joined == separator:
                 if n_items == 1 and texts_to_translate[0] == "": return [""], None
                 error_msg = "Lỗi API: Chỉ trả về separator"; print(error_msg + f" Input: {texts_to_translate[:2]}..."); return None, error_msg
            if translated_joined.startswith(separator): translated_joined = translated_joined[len(separator):].lstrip()

            if not translated_joined:
                 if n_items > 0 and any(t.strip() for t in texts_to_translate):
                     error_msg = f"Lỗi số lượng trả về ({n_items}->0)"; print(error_msg + f" Raw: {raw_response_text[:100]}..."); return None, error_msg
                 else:
                     cleaned_parts = [""] * n_items
            else:
                 cleaned_parts = [part.strip() for part in translated_joined.split(separator)]

            if len(cleaned_parts) == n_items:
                 return cleaned_parts, None
            else:
                 if n_items == 1 and separator not in raw_response_text:
                     print(f"API Warning: n=1 item, no separator. Assuming full response. Raw: >>>{raw_response_text[:200]}<<<")
                     return [raw_response_text.strip()], None
                 error_msg = f"Lỗi số lượng trả về ({len(cleaned_parts)}/{n_items})"
                 print(f"API Error: Mismatched return count. Input ({n_items}): {texts_to_translate[:2]}... Raw: >>>{raw_response_text[:200]}<<< Split ({len(cleaned_parts)}): {cleaned_parts[:2]}...")
                 return None, error_msg

        except google_exceptions.ResourceExhausted as e_quota: print(f"API Quota/Rate Limit Error (429): {e_quota}"); return None, "RATE_LIMIT_PAUSE"
        except google_exceptions.InvalidArgument as e_arg: print(f"API Invalid Argument Error: {e_arg}"); return None, f"Lỗi Invalid Argument API: {str(e_arg)[:100]}..."
        except google_exceptions.GoogleAPIError as e_google_api: print(f"Generic Google API Error: {e_google_api}"); return None, f"Lỗi API Google: {str(e_google_api)[:100]}..."
        except Exception as e_api: print(f"Unhandled API Error: {e_api}"); traceback.print_exc(); return None, f"Lỗi API không xác định: {str(e_api)[:100]}..."


    def process_file_translation_only(self):
        self.last_api_call_time = 0; translation_count = 0; processed_count = 0; api_error_occurred = False
        try:
            filepath = self.source_file_path.get()
            if not filepath: self.after(0, self.finalize_translation); return
            target_language = self.target_lang.get()

            self.after(0, self.update_status, "Đang phát hiện ngôn ngữ (từ mục đã chọn)...")
            source_lang_text_sample = ""; detection_text_limit = 1500
            translatable_items_info = []; data_for_translation_prep = list(self.translation_data)

            for index, data_item in enumerate(data_for_translation_prep):
                 if len(data_item) < 7: continue

                 token_info, original_text, current_status, _, item_id, exclude_user, is_suspicious = data_item

                 if exclude_user:
                      if not any(s in str(current_status) for s in ["Hoàn thành", "Lỗi", "Bỏ qua", "Rỗng", "Hoàn nguyên", "Nghi ngờ"]):
                          skip_reason = "Bỏ qua (Người dùng)"
                          if current_status != "Bỏ qua (Người dùng)":
                              if self.auto_exclude_comments_var.get() and token_info.type == tokenize.COMMENT:
                                  skip_reason = "Bỏ qua (Lọc #)"

                          self.translation_data[index][2] = skip_reason
                          self.translation_data[index][3] = self.translation_data[index][1]
                          self.after(0, self.update_translation_item_result, index, skip_reason, self.translation_data[index][1] , "skipped")
                      continue

                 if not any(s in str(current_status) for s in ["Hoàn thành", "Lỗi", "Hoàn nguyên", "Bỏ qua", "Rỗng"]):
                    text_to_translate, prefix, suffix, is_comment = "", "", "", False
                    if token_info.type == tokenize.COMMENT:
                        match = re.match(r'^(\s*#\s*)', original_text); prefix = match.group(1) if match else "# "
                        text_to_translate = original_text[len(prefix):]; is_comment = True
                    elif token_info.type == tokenize.STRING:
                         try:
                            prefix_match = re.match(r"^[urfURFbB]{1,2}", original_text); prefix_start = prefix_match.group(0) if prefix_match else ""
                            str_content = original_text[len(prefix_start):]
                            quotes = ('"""', "'''", '"', "'"); found_q = False
                            for q in quotes:
                                if str_content.startswith(q) and str_content.endswith(q) and len(str_content)>=2*len(q):
                                    prefix=prefix_start+q; suffix=q; text_to_translate=str_content[len(q):-len(q)]; found_q=True; break
                            if not found_q: continue
                         except Exception as e: print(f"Trans prep parse err L{token_info.start[0]}:{e}"); continue

                    if text_to_translate.strip():
                        if len(source_lang_text_sample) <= detection_text_limit:
                             source_lang_text_sample += text_to_translate + " ";
                        translatable_items_info.append((index, text_to_translate, prefix, suffix, is_comment, item_id))
                        self.after(0, self.update_translation_item_status, index, "Đang xử lý...", "processing")
                    else:
                         empty_status = "Rỗng/Whitespace"
                         self.translation_data[index][2] = empty_status
                         self.translation_data[index][3] = self.translation_data[index][1]
                         self.after(0, self.update_translation_item_result, index, empty_status, self.translation_data[index][1] , "empty")

                 else:
                      processed_count +=1

            detected_lang_display = "N/A"
            if source_lang_text_sample.strip():
                try: detected_lang_display = detect(source_lang_text_sample.strip())
                except LangDetectException: detected_lang_display = "Không xác định"
                except Exception as e_det: print(f"Lang detect error: {e_det}"); detected_lang_display = "Lỗi Detect"
            else: detected_lang_display = "Không có text (chọn)"
            self.after(0, self.detected_source_lang.set, detected_lang_display)

            total_items_to_translate = len(translatable_items_info)
            total_selected_for_processing = sum(1 for item in self.translation_data if len(item)>=7 and not item[5])

            if total_items_to_translate == 0:
                self.after(0, self.update_status, f"Không có mục nào mới/hợp lệ được chọn (☑) để dịch.")
                self.after(0, self.finalize_translation); return
            else:
                self.after(0, self.update_status, f"Bắt đầu dịch (Vòng 1) {total_items_to_translate} mục đã chọn...")

            batch_start = 0
            while batch_start < total_items_to_translate:
                if self.stop_flag: break
                while self.is_paused and not self.stop_flag: time.sleep(0.1)
                if self.stop_flag: break
                batch_end = min(batch_start + self.batch_size, total_items_to_translate)
                current_batch_info = translatable_items_info[batch_start:batch_end]
                texts_to_translate_batch = [item[1] for item in current_batch_info]
                translated_results = None; batch_api_error = None; batch_attempt = 0

                while batch_attempt <= MAX_BATCH_RETRIES:
                    if self.stop_flag: break
                    while self.is_paused and not self.stop_flag: time.sleep(0.1)
                    if self.stop_flag: break
                    current_time = time.time(); time_since_last_call = current_time - self.last_api_call_time
                    if self.seconds_per_request > 0 and time_since_last_call < self.seconds_per_request: time.sleep(self.seconds_per_request - time_since_last_call)
                    if self.stop_flag: break
                    self.last_api_call_time = time.time()

                    batch_status_msg = f"Đang dịch batch {batch_start//self.batch_size + 1}/{total_items_to_translate//self.batch_size + 1}"
                    if batch_attempt > 0: batch_status_msg += f" (Thử lại batch {batch_attempt})"
                    self.after(0, self.update_status, batch_status_msg + "...")

                    translated_results, batch_api_error = self._call_gemini_api(texts_to_translate_batch, target_language)

                    if translated_results is not None: batch_api_error = None; break
                    elif batch_api_error == "RATE_LIMIT_PAUSE":
                        pause_msg = "Lỗi Quota (429). Tạm dừng 10 giây..."; print(pause_msg); self.after(0, self.update_status, pause_msg)
                        pause_start_time = time.time()
                        while time.time() - pause_start_time < 10:
                             if self.stop_flag: break; time.sleep(0.1)
                        if self.stop_flag: break
                        batch_api_error = None; print("Tiếp tục thử lại batch..."); self.after(0, self.update_status, "Tiếp tục thử lại batch..."); continue
                    else:
                        batch_attempt += 1
                        if batch_attempt <= MAX_BATCH_RETRIES:
                             retry_msg = f"Lỗi batch: '{batch_api_error}'. Thử lại sau {RETRY_DELAY_SECONDS}s..."; print(retry_msg); self.after(0, self.update_status, retry_msg)
                             time.sleep(RETRY_DELAY_SECONDS);
                        else:
                             retry_fail_msg = f"Lỗi dịch batch sau {MAX_BATCH_RETRIES+1} lần thử. Thử dịch từng item..."; print(retry_fail_msg); self.after(0, self.update_status, retry_fail_msg); api_error_occurred = True; break
                if self.stop_flag: break

                if translated_results:
                    for i, translated_text_only in enumerate(translated_results):
                         if i >= len(current_batch_info): break
                         item_index, _, item_prefix, item_suffix, item_is_comment, item_id = current_batch_info[i]
                         safe_translated_text = str(translated_text_only).strip()
                         translated_full = item_prefix + safe_translated_text + (item_suffix if not item_is_comment else "")
                         if item_index < len(self.translation_data) and len(self.translation_data[item_index]) >= 7:
                            self.translation_data[item_index][2] = "Hoàn thành"; self.translation_data[item_index][3] = translated_full
                         self.after(0, self.update_translation_item_result, item_index, "Hoàn thành", translated_full, "done")
                         translation_count += 1
                    processed_count += len(current_batch_info)
                    self.after(0, self.update_status, f"Đã xử lý (Vòng 1) {processed_count}/{total_selected_for_processing} mục chọn ({translation_count} OK)...")

                elif batch_api_error:
                    for item_info in current_batch_info:
                         if self.stop_flag: break
                         while self.is_paused and not self.stop_flag: time.sleep(0.1)
                         if self.stop_flag: break
                         item_index, item_text, item_prefix, item_suffix, item_is_comment, item_id = item_info
                         self.after(0, self.update_translation_item_status, item_index, "Đang thử lại...", "processing")
                         item_translated_result = None; item_api_error_final = None; item_attempt = 0

                         while item_attempt <= MAX_ITEM_RETRIES:
                             if self.stop_flag: break
                             while self.is_paused and not self.stop_flag: time.sleep(0.1)
                             if self.stop_flag: break
                             current_time = time.time(); time_since_last_call = current_time - self.last_api_call_time
                             if self.seconds_per_request > 0 and time_since_last_call < self.seconds_per_request: time.sleep(self.seconds_per_request - time_since_last_call)
                             if self.stop_flag: break
                             self.last_api_call_time = time.time()

                             item_translated_result_list, item_api_error = self._call_gemini_api([item_text], target_language)

                             if item_translated_result_list:
                                 item_translated_result = item_translated_result_list[0]; item_api_error_final = None; break
                             elif item_api_error == "RATE_LIMIT_PAUSE":
                                 pause_msg = f"Lỗi Quota (429) item {item_index+1}. Tạm dừng 10 giây..."; print(pause_msg); self.after(0, self.update_status, pause_msg)
                                 pause_start_time = time.time();
                                 while time.time() - pause_start_time < 10:
                                      if self.stop_flag: break; time.sleep(0.1)
                                 if self.stop_flag: break
                                 item_api_error_final = None; print(f"Tiếp tục thử lại item {item_index+1}..."); self.after(0, self.update_status, f"Tiếp tục thử lại item {item_index+1}..."); continue
                             else:
                                 item_api_error_final = item_api_error; item_attempt += 1
                                 if item_attempt <= MAX_ITEM_RETRIES: print(f"Lỗi dịch item {item_index+1}: '{item_api_error}'. Thử lại..."); time.sleep(RETRY_DELAY_SECONDS);
                                 else:
                                     final_item_error = f"Lỗi API (V1): {item_api_error_final or 'Unknown'}"; print(f"Bỏ qua item {item_index+1} (V1) sau lỗi: {item_api_error_final}")
                                     original_content = "";
                                     if item_index < len(self.translation_data) and len(self.translation_data[item_index]) >= 7:
                                         original_content = self.translation_data[item_index][1]
                                         self.translation_data[item_index][2] = final_item_error
                                         self.translation_data[item_index][3] = original_content
                                     self.after(0, self.update_translation_item_result, item_index, final_item_error, original_content, "retry_error"); api_error_occurred = True; break
                         if self.stop_flag: break

                         if item_translated_result is not None:
                             safe_translated_text = str(item_translated_result).strip(); translated_full = item_prefix + safe_translated_text + (item_suffix if not item_is_comment else "")
                             if item_index < len(self.translation_data) and len(self.translation_data[item_index]) >= 7:
                                 self.translation_data[item_index][2] = "Hoàn thành (thử lại)"; self.translation_data[item_index][3] = translated_full
                             self.after(0, self.update_translation_item_result, item_index, "Hoàn thành (thử lại)", translated_full, "done"); translation_count += 1
                         processed_count += 1
                         self.after(0, self.update_status, f"Đã xử lý (Vòng 1) {processed_count}/{total_selected_for_processing} mục chọn ({translation_count} OK)...")

                if self.stop_flag: break
                batch_start = batch_end

            if not self.stop_flag:
                items_for_second_pass_info = []; current_data_snapshot = list(self.translation_data)
                for index, data_item in enumerate(current_data_snapshot):
                    if len(data_item) < 7 or data_item[5]: continue

                    token_info, original_text, current_status, _, item_id, _, is_suspicious = data_item
                    if isinstance(current_status, str) and any(e_stat in current_status for e_stat in ["Lỗi API", "API bị chặn", "Quota/Rate Limit", "Invalid Argument", "Chỉ trả về separator", "Lỗi số lượng"]):
                        text_to_translate, prefix, suffix, is_comment = "", "", "", False;
                        if token_info.type == tokenize.COMMENT: match=re.match(r'^(\s*#\s*)',original_text); prefix=match.group(1) if match else "# "; text_to_translate=original_text[len(prefix):]; is_comment=True
                        elif token_info.type == tokenize.STRING:
                             try:
                                prefix_match=re.match(r"^[urfURFbB]{1,2}",original_text); prefix_start=prefix_match.group(0) if prefix_match else ""
                                str_content=original_text[len(prefix_start):]; quotes=('"""',"'''",'"',"'"); found=False
                                for q in quotes:
                                    if str_content.startswith(q) and str_content.endswith(q) and len(str_content)>=2*len(q):
                                        prefix=prefix_start+q; suffix=q; text_to_translate=str_content[len(q):-len(q)]; found=True; break
                                if not found: continue
                             except Exception as e_parse_r2: print(f"R2 parse err L{token_info.start[0]}:{e_parse_r2}"); continue
                        if text_to_translate.strip(): items_for_second_pass_info.append((index, text_to_translate, prefix, suffix, is_comment, item_id))

                total_items_to_retry_r2 = len(items_for_second_pass_info)
                if total_items_to_retry_r2 > 0:
                    self.after(0, self.update_status, f"Hoàn tất V1. Thử lại {total_items_to_retry_r2} mục lỗi (Vòng 2)..."); processed_r2_count = 0
                    for item_info_r2 in items_for_second_pass_info:
                        if self.stop_flag: break
                        while self.is_paused and not self.stop_flag: time.sleep(0.1)
                        if self.stop_flag: break
                        item_index, item_text, item_prefix, item_suffix, item_is_comment, item_id = item_info_r2
                        self.after(0, self.update_translation_item_status, item_index, "Đang thử lại (V2)...", "processing")
                        item_translated_result_r2 = None; item_api_error_final_r2 = None; item_attempt_r2 = 0
                        while item_attempt_r2 <= MAX_ITEM_RETRIES:
                            if self.stop_flag: break
                            while self.is_paused and not self.stop_flag: time.sleep(0.1)
                            if self.stop_flag: break
                            current_time = time.time(); time_since_last_call = current_time - self.last_api_call_time
                            if self.seconds_per_request > 0 and time_since_last_call < self.seconds_per_request: time.sleep(self.seconds_per_request - time_since_last_call)
                            if self.stop_flag: break
                            self.last_api_call_time = time.time()

                            item_translated_result_list_r2, item_api_error_r2 = self._call_gemini_api([item_text], target_language)

                            if item_translated_result_list_r2: item_translated_result_r2 = item_translated_result_list_r2[0]; item_api_error_final_r2 = None; break
                            elif item_api_error_r2 == "RATE_LIMIT_PAUSE":
                                pause_msg = f"Lỗi Quota (429) item {item_index+1} (V2). Tạm dừng 10 giây..."; print(pause_msg); self.after(0, self.update_status, pause_msg)
                                pause_start_time = time.time();
                                while time.time() - pause_start_time < 10:
                                     if self.stop_flag: break; time.sleep(0.1)
                                if self.stop_flag: break
                                item_api_error_final_r2 = None; print(f"Tiếp tục thử lại item {item_index+1} (V2)..."); self.after(0, self.update_status, f"Tiếp tục thử lại item {item_index+1} (V2)..."); continue
                            else:
                                item_api_error_final_r2 = item_api_error_r2; item_attempt_r2 += 1
                                if item_attempt_r2 <= MAX_ITEM_RETRIES: print(f"Lỗi dịch item {item_index+1} (V2): '{item_api_error_r2}'. Thử lại..."); time.sleep(RETRY_DELAY_SECONDS);
                                else:
                                    final_item_error_r2 = f"Lỗi API (V2): {item_api_error_final_r2 or 'Unknown'}"; print(f"BỎ QUA item {item_index+1} sau lỗi V2: {item_api_error_final_r2}")
                                    original_content = "";
                                    if item_index < len(self.translation_data) and len(self.translation_data[item_index]) >= 7:
                                        original_content = self.translation_data[item_index][1]
                                        self.translation_data[item_index][2] = final_item_error_r2
                                        self.translation_data[item_index][3] = original_content
                                    self.after(0, self.update_translation_item_result, item_index, final_item_error_r2, original_content, "error"); api_error_occurred = True; break
                        if self.stop_flag: break
                        if item_translated_result_r2 is not None:
                            safe_translated_text_r2 = str(item_translated_result_r2).strip(); translated_full_r2 = item_prefix + safe_translated_text_r2 + (item_suffix if not item_is_comment else "")
                            if item_index < len(self.translation_data) and len(self.translation_data[item_index]) >= 7:
                                self.translation_data[item_index][2] = "Hoàn thành (Vòng 2)"
                                self.translation_data[item_index][3] = translated_full_r2
                            self.after(0, self.update_translation_item_result, item_index, "Hoàn thành (Vòng 2)", translated_full_r2, "done"); translation_count += 1
                        processed_r2_count += 1
                        processed_count += 1
                        self.after(0, self.update_status, f"Đã xử lý (Vòng 2) {processed_r2_count}/{total_items_to_retry_r2} ({translation_count} tổng OK)...")
                    if self.stop_flag: self.after(0, self.update_status, f"Đã dừng trong Vòng 2. ({translation_count} tổng OK)")
                    elif total_items_to_retry_r2 > 0: self.after(0, self.update_status, f"Hoàn tất Vòng 2. ({translation_count} tổng OK)")

            final_status = "";
            final_success_count = sum(1 for item in self.translation_data if len(item)>=7 and isinstance(item[2], str) and item[2].startswith("Hoàn thành"))
            skipped_count = sum(1 for item in self.translation_data if len(item)>=7 and item[5])
            error_count = sum(1 for item in self.translation_data if len(item)>=7 and not item[5] and isinstance(item[2], str) and "Lỗi" in item[2])

            if self.stop_flag:
                 status_text = self.status_bar['text'] if hasattr(self, 'status_bar') else ""
                 final_status = status_text if "Vòng 2" in status_text and "Đã dừng" in status_text else f"Đã dừng. {final_success_count} OK, {skipped_count} bỏ qua, {error_count} lỗi."
            elif api_error_occurred:
                 final_status = f"Hoàn tất với lỗi. {final_success_count} OK, {skipped_count} bỏ qua, {error_count} lỗi."
            else:
                 final_status = f"Hoàn tất! {final_success_count} OK, {skipped_count} bỏ qua."

            if final_status: self.after(0, self.update_status, final_status)
            self.after(0, self.finalize_translation)

        except FileNotFoundError:
             self.after(0, self.update_status, f"Lỗi: Không tìm thấy file {self.source_file_path.get()}"); self.after(0, lambda: Messagebox.show_error(f"Không tìm thấy file:\n{self.source_file_path.get()}", "Lỗi File", parent=self)); self.after(0, self.finalize_translation)
        except Exception as e_general:
             print(f"Lỗi không xác định trong process_file_translation_only: {e_general}"); traceback.print_exc();
             self.after(0, self.update_status, f"Lỗi dịch không xác định: {e_general}");
             self.after(0, lambda: Messagebox.show_error(f"Đã xảy ra lỗi không mong muốn khi dịch:\n{e_general}", "Lỗi Nghiêm trọng", parent=self));
             self.after(0, self.finalize_translation)


    def finalize_translation(self):
        self.is_translating = False; self.is_paused = False
        can_interact = bool(self.source_file_path.get())
        if hasattr(self, 'btn_translate'):
             btn_text = "Dịch" if self.scan_complete else "Quét / Dịch"
             btn_state = NORMAL if can_interact else DISABLED
             self.btn_translate.config(text=btn_text, state=btn_state)
        if hasattr(self, 'btn_scan_comments'): self.btn_scan_comments.config(state=NORMAL if can_interact else DISABLED)
        if hasattr(self, 'btn_pause_resume'): self.btn_pause_resume.config(state=DISABLED, text="Tạm dừng")
        if hasattr(self, 'btn_stop'): self.btn_stop.config(state=DISABLED)
        can_save = bool(can_interact and self.scan_complete and self.translation_data)
        if hasattr(self, 'btn_save_trans'): self.btn_save_trans.config(state=NORMAL if can_save else DISABLED)
        if hasattr(self, 'btn_run_test'): self.btn_run_test.config(state=NORMAL if can_save else DISABLED)

        cmt_exists = bool(self.comment_data)
        if hasattr(self, 'btn_check_all_comments'): self.btn_check_all_comments.config(state=NORMAL if cmt_exists else DISABLED)
        if hasattr(self, 'btn_uncheck_all_comments'): self.btn_uncheck_all_comments.config(state=NORMAL if cmt_exists else DISABLED)
        if hasattr(self, 'btn_save_comments'): self.btn_save_comments.config(state=NORMAL if cmt_exists else DISABLED)

        if self.scan_complete and self.translation_data:
            has_comments = any(item[0].type == tokenize.COMMENT for item in self.translation_data if len(item)>0)
            has_strings = self.scan_produced_strings

            if hasattr(self, 'chk_auto_exclude_comments'):
                 self.chk_auto_exclude_comments.config(state=NORMAL if has_comments else DISABLED)

            if hasattr(self, 'btn_select_all_trans'):
                self.btn_select_all_trans.config(state=NORMAL)
            if hasattr(self, 'btn_deselect_all_trans'):
                self.btn_deselect_all_trans.config(state=NORMAL)
        else:
             if hasattr(self, 'chk_auto_exclude_comments'):
                 self.chk_auto_exclude_comments.config(state=DISABLED)
             if hasattr(self, 'btn_select_all_trans'):
                self.btn_select_all_trans.config(state=DISABLED)
             if hasattr(self, 'btn_deselect_all_trans'):
                self.btn_deselect_all_trans.config(state=DISABLED)


        if hasattr(self, 'status_bar'):
             current = self.status_bar['text']
             if not any(s in current for s in ["Hoàn tất", "Đã dừng", "lỗi", "OK", "Sẵn sàng lưu", "Đã lưu", "Quét xong"]):
                  final = "Sẵn sàng."
                  if self.stop_flag: final = "Đã dừng. Sẵn sàng lưu." if can_save else "Đã dừng."
                  elif can_save: final = "Sẵn sàng lưu file."
                  elif self.scan_complete: final = "Sẵn sàng dịch hoặc lưu."
                  self.update_status(final)
        self.stop_flag = False


    def extract_code_elements(self, filepath, string_mode="safe_ast", target_lines: set[int] | None = None):
        elements = []
        ast_translatable_nodes = {}
        content_filtered_count = 0
        processed_token_count = 0
        ast_analysis_failed = False

        if string_mode == "safe_ast":
            try:
                with open(filepath, 'r', encoding='utf-8') as f_ast: file_content_for_ast = f_ast.read()
                tree = ast.parse(file_content_for_ast, filename=filepath)
                add_parent_pointers(tree)
                visitor = TranslatableStringVisitor()
                visitor.visit(tree)
                ast_translatable_nodes = visitor.translatable_nodes
            except SyntaxError as e_ast:
                 print(f"SyntaxError during AST parsing: {e_ast}. Cannot perform safe string analysis.")
                 string_mode = "none"; ast_translatable_nodes = {}; ast_analysis_failed = True
            except FileNotFoundError: raise
            except Exception as e_ast_general:
                 print(f"Error during AST analysis: {e_ast_general}"); traceback.print_exc()
                 ast_translatable_nodes = {}; ast_analysis_failed = True

        try:
            with open(filepath, 'rb') as file_bytes:
                tokens = tokenize.tokenize(file_bytes.readline)
                for token_info in tokens:
                    processed_token_count += 1; current_line = token_info.start[0]
                    if token_info.type == tokenize.COMMENT:
                        if len(token_info.string.strip()) > 1:
                            elements.append((token_info, token_info.string))
                    elif token_info.type == tokenize.STRING:
                        is_f_string = token_info.string.lower().startswith(('f"', "f'"))
                        if is_f_string: continue
                        if string_mode == "all": elements.append((token_info, token_info.string))
                        elif string_mode == "safe_ast" and not ast_analysis_failed:
                            ast_node_info = ast_translatable_nodes.get(current_line)
                            if ast_node_info:
                                ast_node, ast_string_value = ast_node_info
                                token_value_eval = None
                                try: token_value_eval = ast.literal_eval(token_info.string)
                                except: pass
                                if ast_node.lineno == current_line and \
                                   ast_node.col_offset == token_info.start[1] and \
                                   token_value_eval is not None and \
                                   ast_string_value == token_value_eval:
                                    if not is_likely_technical_string(ast_string_value) and not is_meaningless_string(ast_string_value):
                                         elements.append((token_info, token_info.string))
                                    else: content_filtered_count += 1
        except tokenize.TokenError as e_tok: print(f"Token Error: {e_tok}"); raise
        except FileNotFoundError: raise
        except Exception as e_read: print(f"File Read Error: {e_read}"); raise

        return elements, content_filtered_count, 0, processed_token_count


    def run_test_translation(self):
        """Initiates a test run of the potentially translated code."""
        if self.is_translating:
            Messagebox.show_info("Vui lòng đợi quá trình dịch hoàn tất.", "Đang chạy", parent=self)
            return
        if not self.source_file_path.get():
            Messagebox.show_warning("Chưa chọn file gốc.", parent=self)
            return
        if not self.translation_data:
            Messagebox.show_warning("Không có dữ liệu scan để chạy thử.", parent=self)
            return
        if not self.scan_complete:
            Messagebox.show_warning("Vui lòng Quét file trước khi chạy thử.", parent=self)
            return

        self.update_status("Chuẩn bị chạy thử nghiệm...")
        self.btn_run_test.config(state=DISABLED)
        self.btn_save_trans.config(state=DISABLED)
        self.btn_translate.config(state=DISABLED)

        thread = threading.Thread(target=self._execute_test_run_thread, daemon=True)
        thread.start()

    def _execute_test_run_thread(self):
        """
        Hàm này chạy trong một thread riêng để:
        1. Đọc file gốc.
        2. Tạo nội dung code mới dựa trên dữ liệu dịch hiện tại.
        3. Lưu code mới vào một file tạm thời.
        4. Thực thi file tạm thời bằng trình thông dịch Python.
        5. Bắt output (stdout) và lỗi (stderr) từ quá trình thực thi.
        6. Hiển thị output/lỗi trong cửa sổ mới.
        7. Xóa file tạm thời.
        8. Cập nhật trạng thái giao diện người dùng.
        """
        temp_file_path = None
        original_path = Path(self.source_file_path.get())
        run_success = False
        output_stdout = ""
        output_stderr = ""

        try:
            self.after(0, self.update_status, "Đang tạo code tạm thời...")

            original_lines = []
            used_encoding = 'utf-8'
            try:
                with open(original_path, 'r', encoding=used_encoding) as f:
                    original_lines = f.readlines()
            except UnicodeDecodeError:
                self.after(0, self.update_status, "Cảnh báo: Đọc file gốc bằng UTF-8 lỗi, thử encoding mặc định...")
                try:
                    used_encoding = None
                    with open(original_path, 'r', encoding=used_encoding) as f:
                        original_lines = f.readlines()
                except Exception as e_read_fallback:
                    error_msg = f"Lỗi đọc file gốc (cả UTF-8 và mặc định): {e_read_fallback}"
                    self.after(0, self.update_status, error_msg)
                    self.after(0, lambda: Messagebox.show_error(f"Không thể đọc file gốc:\n{e_read_fallback}", "Lỗi File", parent=self))
                    self.after(0, self.finalize_test_run, False)
                    return
            except Exception as e_read_initial:
                error_msg = f"Lỗi đọc file gốc: {e_read_initial}"
                self.after(0, self.update_status, error_msg)
                self.after(0, lambda: Messagebox.show_error(f"Không thể đọc file gốc:\n{e_read_initial}", "Lỗi File", parent=self))
                self.after(0, self.finalize_test_run, False)
                return

            current_data_snapshot = [item for item in self.translation_data if len(item) >= 6]
            generated_lines, replacements, items_processed = self._generate_output_lines(original_lines, current_data_snapshot)
            code_to_run = "".join(generated_lines)

            if not code_to_run.strip():
                 self.after(0, self.update_status, "Lỗi: Code tạo ra rỗng.")
                 self.after(0, lambda: Messagebox.show_error("Code được tạo ra để chạy thử là rỗng.", "Lỗi Code Rỗng", parent=self))
                 self.after(0, self.finalize_test_run, False)
                 return

            self.after(0, self.update_status, "Đang tạo file tạm...")
            with tempfile.NamedTemporaryFile(mode='w', suffix=".py", encoding='utf-8', delete=False) as temp_file:
                temp_file_path = temp_file.name
                temp_file.write(code_to_run)

            if not temp_file_path:
                raise IOError("Không thể tạo file tạm.")

            self.after(0, self.update_status, f"Đang chạy file thử nghiệm: {os.path.basename(temp_file_path)}...")
            script_dir = os.path.dirname(original_path)

            child_env = os.environ.copy()
            child_env['PYTHONIOENCODING'] = 'utf-8'

            result = subprocess.run(
                ['python', temp_file_path],
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='replace',
                cwd=script_dir,
                env=child_env
            )

            output_stdout = result.stdout
            output_stderr = result.stderr
            run_success = True

            status_msg = "Chạy thử hoàn tất."
            if result.returncode != 0:
                status_msg += f" (Có lỗi runtime - Mã lỗi: {result.returncode})"
            self.after(0, self.update_status, status_msg)

        except FileNotFoundError:
            error_msg = "LỖI: Không tìm thấy trình thông dịch 'python'.\nHãy đảm bảo Python đã được cài đặt và thêm vào PATH hệ thống."
            output_stderr = error_msg
            self.after(0, self.update_status, "Lỗi: Không tìm thấy 'python'.")
            self.after(0, lambda: Messagebox.show_error(error_msg, "Lỗi Thực Thi", parent=self))
        except IOError as e_io:
            error_msg = f"LỖI IO: Không thể tạo hoặc ghi file tạm.\n{e_io}"
            output_stderr = error_msg
            self.after(0, self.update_status, "Lỗi: Không thể tạo file tạm.")
            self.after(0, lambda: Messagebox.show_error(error_msg, "Lỗi File Tạm", parent=self))
        except Exception as e:
            print(f"Lỗi không xác định khi chạy thử: {e}")
            traceback.print_exc()
            error_msg = f"LỖI KHÔNG XÁC ĐỊNH:\n{traceback.format_exc()}"
            output_stderr = error_msg
            self.after(0, self.update_status, f"Lỗi không xác định khi chạy thử: {e}")
            self.after(0, lambda: Messagebox.show_error(f"Đã xảy ra lỗi không mong muốn khi chạy thử:\n{e}", "Lỗi Nghiêm trọng", parent=self))
        finally:

            if temp_file_path and os.path.exists(temp_file_path):
                try:
                    os.remove(temp_file_path)
                    print(f"Đã xóa file tạm: {temp_file_path}")
                except OSError as e_del:
                    print(f"Lỗi khi xóa file tạm '{temp_file_path}': {e_del}")

            self.after(0, self._display_test_output, output_stdout, output_stderr)

            self.after(0, self.finalize_test_run, run_success)

    def finalize_test_run(self, success):
        """Resets button states after test run finishes or fails."""
        can_interact = bool(self.source_file_path.get())
        can_save_or_test = bool(can_interact and self.scan_complete and self.translation_data)

        if hasattr(self, 'btn_run_test'):
            self.btn_run_test.config(state=NORMAL if can_save_or_test else DISABLED)
        if hasattr(self, 'btn_save_trans'):
            self.btn_save_trans.config(state=NORMAL if can_save_or_test else DISABLED)
        if hasattr(self, 'btn_translate'):
            btn_text = "Dịch" if self.scan_complete else "Quét / Dịch"
            self.btn_translate.config(text=btn_text, state=NORMAL if can_interact else DISABLED)
        if hasattr(self, 'btn_pause_resume'): self.btn_pause_resume.config(state=DISABLED)
        if hasattr(self, 'btn_stop'): self.btn_stop.config(state=DISABLED)

        current_status = self.status_bar['text'] if hasattr(self, 'status_bar') else ""
        if "Chạy thử hoàn tất" not in current_status and "Lỗi" not in current_status:
             self.update_status("Sẵn sàng." if not can_save_or_test else "Chạy thử xong. Sẵn sàng lưu/dịch.")


    def _display_test_output(self, stdout_text, stderr_text):
        """Creates a Toplevel window to display the captured output."""
        output_window = tb.Toplevel(master=self, title="Kết quả Chạy thử")

        output_window.geometry("800x600")
        output_window.transient(self)
        output_window.grab_set()

        content_frame = tb.Frame(output_window, padding=10)
        content_frame.pack(fill=BOTH, expand=True)
        content_frame.rowconfigure(0, weight=1)
        content_frame.columnconfigure(0, weight=1)

        txt_output = ScrolledText(content_frame, wrap=tk.WORD, height=20, width=80,
                                  font=self.app_font or (DEFAULT_SETTINGS["font_family"], DEFAULT_SETTINGS["font_size"]),
                                  relief=tk.SUNKEN, bd=1)
        txt_output.grid(row=0, column=0, sticky="nsew", pady=(0, 10))

        full_output = ""
        if stdout_text:
            full_output += "--- OUTPUT (stdout) ---\n"
            full_output += stdout_text.strip() + "\n\n"
        if stderr_text:
            full_output += "--- ERRORS (stderr) ---\n"
            full_output += stderr_text.strip() + "\n"

        if not full_output.strip():
             full_output = "(Không có output nào được ghi nhận)"

        txt_output.insert(tk.END, full_output)
        txt_output.config(state=tk.DISABLED)

        btn_close = tb.Button(content_frame, text="Đóng", command=output_window.destroy, bootstyle=SECONDARY)
        btn_close.grid(row=1, column=0, sticky=E)

        output_window.focus_set()


    def populate_translation_treeview_initial(self, primary_elements, suspicious_elements):
        self.clear_translation_results()
        item_count = 0; last_item_id = None
        has_comments = False
        has_strings = False

        all_elements_with_suspicion_flag = [(e, False) for e in primary_elements] + [(e, True) for e in suspicious_elements]

        for (token_info, original_text), is_suspicious in all_elements_with_suspicion_flag:
            line, type_name = token_info.start[0], tokenize.tok_name[token_info.type]
            status, translated = "Chờ xử lý", ""
            exclude_from_translation = False
            if is_suspicious:
                status = "Nghi ngờ (AI bỏ qua)"; exclude_from_translation = True

            content = ""
            is_comment = False
            if type_name == "COMMENT":
                 content = re.sub(r'^\s*#\s*', '', original_text).strip()
                 is_comment = True; has_comments = True
            elif type_name == "STRING":
                 has_strings = True
                 if original_text.lower().startswith(('f"', "f'")): content = None
                 else:
                      try: content = ast.literal_eval(original_text)
                      except: content = original_text
            if content is None:
                status, translated = "Bỏ qua (f-string)", original_text; exclude_from_translation = True
            elif content == "" or (isinstance(content, str) and not content.strip()):
                status, translated = "Rỗng/Whitespace", original_text; exclude_from_translation = True

            try:
                if hasattr(self, 'tree_trans'):
                    item_id = self.tree_trans.insert("", END, values=("?", line, original_text, status, translated))
                    self.translation_data.append([token_info, original_text, status, translated, item_id, exclude_from_translation, is_suspicious])
                    self._update_tree_item_display(len(self.translation_data) - 1)
                    item_count += 1; last_item_id = item_id
            except tk.TclError: pass

        if last_item_id and hasattr(self, 'tree_trans') and self.tree_trans.exists(last_item_id): self.tree_trans.see(last_item_id)
        return item_count, has_comments, has_strings


    def apply_comment_filter(self):
        if not hasattr(self, 'tree_trans') or not self.translation_data:
            return

        filter_enabled = self.auto_exclude_comments_var.get()
        updated_count = 0
        currently_excluded_count = 0

        if filter_enabled:
            self.ids_excluded_by_comment_filter.clear()
            for index, data_item in enumerate(self.translation_data):
                if len(data_item) < 7: continue
                token_info, _, current_status, _, item_id, current_exclude_state, is_suspicious_item = data_item

                if token_info.type == tokenize.COMMENT and not current_exclude_state:
                    self.ids_excluded_by_comment_filter.add(item_id)
                    self.translation_data[index][5] = True
                    new_status = "Bỏ qua (Lọc #)"
                    if is_suspicious_item: new_status = "Nghi ngờ (Lọc #)"
                    self.translation_data[index][2] = new_status
                    self._update_tree_item_display(index)
                    updated_count += 1

            currently_excluded_count = sum(1 for item in self.translation_data if len(item) >= 7 and item[0].type == tokenize.COMMENT and item[5])
            status_msg = f"Bộ lọc #comment: {len(self.ids_excluded_by_comment_filter)} mục bị ẩn ({currently_excluded_count} tổng cộng bị bỏ qua)."
        else:
            reverted_count = 0
            items_to_revert = list(self.ids_excluded_by_comment_filter)
            self.ids_excluded_by_comment_filter.clear()

            for item_id_to_revert in items_to_revert:
                found_index = -1
                for i, data in enumerate(self.translation_data):
                    if len(data) >= 5 and data[4] == item_id_to_revert:
                        found_index = i
                        break

                if found_index != -1:
                    data_item = self.translation_data[found_index]
                    if len(data_item) < 7: continue
                    token_info, _, current_status, _, _, current_exclude_state, is_suspicious_item = data_item

                    if current_exclude_state:
                        self.translation_data[found_index][5] = False
                        if is_suspicious_item:
                            self.translation_data[found_index][2] = "Nghi ngờ (AI bỏ qua)"
                        else:
                            self.translation_data[found_index][2] = "Chờ xử lý"
                        self._update_tree_item_display(found_index)
                        reverted_count += 1
                        updated_count += 1

            currently_excluded_count = sum(1 for item in self.translation_data if len(item) >= 7 and item[0].type == tokenize.COMMENT and item[5])
            status_msg = f"Đã tắt bộ lọc #comment ({reverted_count} mục được hiển thị lại, {currently_excluded_count} tổng cộng vẫn bị bỏ qua)."

        if updated_count > 0:
            self.update_status(status_msg)


    def _update_tree_item_display(self, index):
        """Updates the visual representation of a single item in tree_trans based on its data."""
        if not hasattr(self, 'tree_trans'): return
        if index < 0 or index >= len(self.translation_data): return

        data_item = self.translation_data[index]
        if len(data_item) < 7:
             print(f"Warn: Data item {index} has unexpected length ({len(data_item)}), cannot update display.")
             return

        token_info, original_text, status_text, translated_text, item_id, exclude_user, is_suspicious = data_item

        if not self.tree_trans.exists(item_id): return

        include_char = "☐" if exclude_user else "☑"
        include_tag = "unchecked" if exclude_user else "checked"

        status_tag = "pending"
        str_status = str(status_text)

        if exclude_user:
             status_tag = "skipped"
             if is_suspicious: status_tag="suspicious"
        elif is_suspicious and ("Nghi ngờ" in str_status or str_status == "Chờ xử lý (Nghi ngờ)"):
             status_tag = "suspicious"
        elif "Hoàn thành" in str_status: status_tag = "done"
        elif "Lỗi" in str_status: status_tag = "error"
        elif str_status == "Rỗng/Whitespace": status_tag = "empty"
        elif str_status.startswith("Bỏ qua"): status_tag = "skipped"
        elif str_status == "Đang xử lý" or "thử lại" in str_status.lower(): status_tag = "processing"
        elif "Hoàn nguyên" in str_status: status_tag = "reverted"
        elif str_status == "Chờ xử lý": status_tag = "pending"


        line = token_info.start[0]
        original_display = original_text

        values_tuple = (include_char, line, original_display, str_status, translated_text if not exclude_user else original_text)

        try:
            self.tree_trans.item(item_id, values=values_tuple, tags=(include_tag, status_tag))
        except tk.TclError as e:
            print(f"Error updating tree display for item {item_id}: {e}")
        except IndexError as e_idx:
            print(f"Error updating tree values {item_id}: {e_idx}")


    def toggle_translation_item_inclusion(self, event):
        if not hasattr(self, 'tree_trans'): return
        item_id = self.tree_trans.identify_row(event.y)
        if not item_id: return

        target_index = -1
        for i, data in enumerate(self.translation_data):
            if len(data) >= 5 and data[4] == item_id:
                target_index = i; break

        if target_index != -1:
            if len(self.translation_data[target_index]) < 7:
                 print(f"Warn: Data item {target_index} has unexpected length ({len(self.translation_data[target_index])}), cannot toggle.")
                 return

            self.ids_excluded_by_comment_filter.discard(item_id)

            current_exclude_state = self.translation_data[target_index][5]
            new_exclude_state = not current_exclude_state
            self.translation_data[target_index][5] = new_exclude_state

            current_status_text = self.translation_data[target_index][2]
            new_status_text = current_status_text
            is_suspicious_item = self.translation_data[target_index][6]

            if new_exclude_state:
                if not any(s in str(current_status_text) for s in ["Bỏ qua", "Rỗng", "Hoàn nguyên"]):
                     new_status_text = "Bỏ qua (Người dùng)"
            else:
                 if str(current_status_text).startswith("Bỏ qua"):
                    is_empty = False
                    is_fstring = False
                    original_text_local = self.translation_data[target_index][1]
                    token_type_local = self.translation_data[target_index][0].type

                    if token_type_local == tokenize.STRING:
                        is_fstring = original_text_local.lower().startswith(('f"', "f'"))
                        try:
                            content_eval = ast.literal_eval(original_text_local)
                            is_empty = (not content_eval or not content_eval.strip())
                        except: pass

                    if is_fstring:
                         new_status_text = "Bỏ qua (f-string)"
                    elif is_empty:
                         new_status_text = "Rỗng/Whitespace"
                    elif is_suspicious_item:
                         new_status_text = "Nghi ngờ (AI bỏ qua)"
                    else:
                         new_status_text = "Chờ xử lý"

                 elif is_suspicious_item and "Nghi ngờ" in str(current_status_text):
                     pass
                 elif any(s in str(current_status_text) for s in ["Hoàn thành", "Lỗi", "Hoàn nguyên"]):
                      pass

            self.translation_data[target_index][2] = new_status_text

            self._update_tree_item_display(target_index)


    def select_all_trans_items(self):
        """Marks all items in the translation list for inclusion (sets exclude_user=False)."""
        if not self.translation_data: return
        updated_count = 0
        for index, data_item in enumerate(self.translation_data):
            if len(data_item) >= 7 and data_item[5]:
                item_id = data_item[4]
                self.ids_excluded_by_comment_filter.discard(item_id)

                self.translation_data[index][5] = False
                current_status_text = str(data_item[2])
                if current_status_text.startswith("Bỏ qua"):
                    is_empty = False
                    is_fstring = False
                    original_text_local = self.translation_data[index][1]
                    token_type_local = self.translation_data[index][0].type
                    if token_type_local == tokenize.STRING:
                        is_fstring = original_text_local.lower().startswith(('f"', "f'"))
                        try:
                             content_eval = ast.literal_eval(original_text_local)
                             is_empty = (not content_eval or not content_eval.strip())
                        except: pass

                    if not is_fstring and not is_empty:
                        is_suspicious_item = data_item[6]
                        if is_suspicious_item:
                            self.translation_data[index][2] = "Nghi ngờ (AI bỏ qua)"
                        else:
                            self.translation_data[index][2] = "Chờ xử lý"

                self._update_tree_item_display(index)
                updated_count += 1
        self.update_status(f"Đã chọn dịch tất cả ({updated_count} mục được chuyển sang ☑).")

    def deselect_all_trans_items(self):
        """Marks all items in the translation list for exclusion (sets exclude_user=True)."""
        if not self.translation_data: return
        updated_count = 0
        for index, data_item in enumerate(self.translation_data):
             if len(data_item) >= 7 and not data_item[5]:
                 self.translation_data[index][5] = True
                 current_status_text = str(data_item[2])
                 if not any(s in current_status_text for s in ["Hoàn thành", "Lỗi", "Hoàn nguyên", "Bỏ qua", "Rỗng"]):
                      self.translation_data[index][2] = "Bỏ qua (Người dùng)"
                 self._update_tree_item_display(index)
                 updated_count += 1
        self.update_status(f"Đã bỏ chọn dịch tất cả ({updated_count} mục được chuyển sang ☐).")


    def update_translation_item_status(self, index, status_text, status_tag):
         if index < len(self.translation_data) and len(self.translation_data[index]) >= 7:
             self.translation_data[index][2] = status_text
             self._update_tree_item_display(index)
             item_id = self.translation_data[index][4]
             if hasattr(self, 'tree_trans') and self.tree_trans.exists(item_id):
                 try: self.tree_trans.see(item_id)
                 except tk.TclError: pass


    def update_translation_item_result(self, index, status_text, translated_text, status_tag):
         if index < len(self.translation_data) and len(self.translation_data[index]) >= 7:
             self.translation_data[index][2] = status_text
             self.translation_data[index][3] = translated_text
             self._update_tree_item_display(index)
             item_id = self.translation_data[index][4]
             if hasattr(self, 'tree_trans') and self.tree_trans.exists(item_id):
                 try: self.tree_trans.see(item_id)
                 except tk.TclError: pass

    def save_translated_file(self):
        if not self.source_file_path.get(): Messagebox.show_warning("Chưa chọn file gốc.", parent=self); return
        if not self.translation_data: Messagebox.show_warning("Không có dữ liệu scan.", parent=self); return
        if not self.scan_complete: Messagebox.show_warning("Vui lòng Quét file trước khi lưu.", parent=self); return

        orig_path = Path(self.source_file_path.get()); lang = self.target_lang.get() or "trans"
        def_name = f"{orig_path.stem}_translated_{lang}{orig_path.suffix}"
        save_path_str = filedialog.asksaveasfilename(title="Lưu file đã dịch", initialdir=orig_path.parent, initialfile=def_name, defaultextension=".py", filetypes=[("Python", "*.py"), ("All", "*.*")])
        if not save_path_str: self.update_status("Hủy lưu."); return
        save_path = Path(save_path_str)
        if save_path.resolve() == orig_path.resolve(): Messagebox.show_error("KHÔNG LƯU! Trùng file gốc.", parent=self); return
        self.update_status(f"Chuẩn bị lưu vào: {save_path.name}...")

        threading.Thread(target=self._execute_save_translated_with_verify, args=(orig_path, save_path), daemon=True).start()


    def _generate_output_lines(self, original_lines, data_snapshot):
        output_lines = list(original_lines)
        replacements = 0
        items_processed = 0

        def get_key(item):
            try: return (item[0].start[0], item[0].start[1])
            except: return (float('inf'), float('inf'))
        try:
            valid_data = [item for item in data_snapshot if len(item) >= 6 and hasattr(item[0], 'start') and hasattr(item[0], 'end')]
            valid_data.sort(key=get_key, reverse=True)
        except Exception as e:
            print(f"Warn: Sort error during output generation: {e}")
            return output_lines, 0, 0

        for item in valid_data:
            items_processed += 1
            token, orig_txt, status, trans_txt, item_id, exclude_user = item[:6]
            should_use_original = exclude_user or not (isinstance(status, str) and status.startswith("Hoàn thành"))
            replace_with = orig_txt if should_use_original else trans_txt
            if replace_with is None: replace_with = orig_txt
            if replace_with is None: continue

            start_ln, end_ln = token.start[0]-1, token.end[0]-1
            start_c, end_c = token.start[1], token.end[1]
            if start_ln < 0 or start_ln >= len(output_lines) or start_ln != end_ln: continue
            curr_line = output_lines[start_ln]
            eff_end_c = end_c; line_len = len(curr_line)
            if eff_end_c > line_len: eff_end_c = line_len
            if curr_line.endswith('\n') and end_c == line_len + 1: eff_end_c = line_len
            if start_c < 0 or start_c > line_len or eff_end_c < start_c: continue

            try:
                output_lines[start_ln] = curr_line[:start_c] + replace_with + curr_line[eff_end_c:]
                if not should_use_original: replacements += 1
            except IndexError:
                 print(f"IndexError during replacement: Line {start_ln}, Cols {start_c}-{eff_end_c}, LineLen {len(curr_line)}")
                 continue

        return output_lines, replacements, items_processed


    def _execute_save_translated_with_verify(self, original_path, save_path):
        try:
            original_lines = []; used_encoding = 'utf-8'
            try:
                with open(original_path, 'r', encoding=used_encoding) as f: original_lines = f.readlines()
            except UnicodeDecodeError:
                try:
                    used_encoding = None
                    with open(original_path, 'r', encoding=used_encoding) as f: original_lines = f.readlines()
                    self.after(0, self.update_status, "Cảnh báo: Đọc bằng encoding mặc định.")
                except Exception as e_fb:
                    self.after(0, self.update_status, f"Lỗi đọc file gốc: {e_fb}"); return

            current_data_snapshot = []
            for item in self.translation_data:
                 if len(item) >= 7:
                     new_item = list(item[:7]) + [False]
                     current_data_snapshot.append(new_item)
                 else: print(f"Warn: Skipping malformed data item during save snapshot: {item}")

            final_output_lines = []; final_replacements = 0; final_items_processed = 0
            verification_attempts = MAX_VERIFICATION_ATTEMPTS if VERIFY_SYNTAX else 1
            parse_successful = False; reverted_lines = set(); reverted_count_total = 0

            while verification_attempts > 0:
                verification_attempts -= 1; is_last_attempt = verification_attempts == 0

                temp_output_lines = list(original_lines); temp_replacements = 0; temp_items_processed = 0
                def get_key(item):
                    try: return (item[0].start[0], item[0].start[1])
                    except: return (float('inf'), float('inf'))
                try: current_data_snapshot.sort(key=get_key, reverse=True)
                except Exception as e: print(f"Warn: Sort error during verification loop: {e}")

                for item in current_data_snapshot:
                    if len(item) < 8: continue
                    token, orig_txt, status, trans_txt, item_id, exclude_user, is_suspicious, temp_revert = item
                    should_use_original = exclude_user or temp_revert or not (isinstance(status, str) and status.startswith("Hoàn thành"))
                    replace_with = orig_txt if should_use_original else trans_txt
                    if replace_with is None: replace_with = orig_txt
                    if replace_with is None: continue

                    start_ln, end_ln = token.start[0]-1, token.end[0]-1
                    start_c, end_c = token.start[1], token.end[1]
                    if start_ln < 0 or start_ln >= len(temp_output_lines) or start_ln != end_ln: continue
                    curr_line = temp_output_lines[start_ln]; eff_end_c = end_c; line_len = len(curr_line)
                    if eff_end_c > line_len: eff_end_c = line_len
                    if curr_line.endswith('\n') and end_c == line_len + 1: eff_end_c = line_len
                    if start_c < 0 or start_c > line_len or eff_end_c < start_c: continue
                    try:
                        temp_output_lines[start_ln] = curr_line[:start_c] + replace_with + curr_line[eff_end_c:]
                        if not should_use_original: temp_replacements += 1
                        temp_items_processed += 1
                    except IndexError: continue

                final_output_lines = temp_output_lines; final_replacements = temp_replacements; final_items_processed = temp_items_processed
                if not VERIFY_SYNTAX: parse_successful = True; break

                self.after(0, self.update_status, f"Đang kiểm tra cú pháp file... (Lần {MAX_VERIFICATION_ATTEMPTS - verification_attempts})")
                code_to_check = "".join(final_output_lines)
                try:
                    ast.parse(code_to_check, filename=str(save_path))
                    parse_successful = True; self.after(0, self.update_status, "Kiểm tra cú pháp thành công."); print("Syntax verification successful."); break
                except SyntaxError as e:
                    err_line = e.lineno; err_msg = e.msg; print(f"SyntaxError near line {err_line}: {err_msg}")
                    self.after(0, self.update_status, f"Lỗi cú pháp dòng {err_line}: {err_msg}. Đang thử hoàn nguyên...")
                    if is_last_attempt:
                         print(f"Max verification attempts reached. Saving with errors.")
                         self.after(0, lambda: Messagebox.show_warning(f"Không thể tự sửa lỗi cú pháp sau {MAX_VERIFICATION_ATTEMPTS} lần.\nLỗi cuối: Dòng {err_line}\n\nFile sẽ được lưu với lỗi.", "Lỗi Cú pháp", parent=self))
                         break
                    reverted_in_this_pass = 0; items_to_revert_indices_snapshot = []
                    for i, item in enumerate(current_data_snapshot):
                         if len(item) >= 8 and hasattr(item[0], 'start'):
                              item_line = item[0].start[0]; status = item[2]; exclude_user = item[5]; temp_revert = item[7]
                              if item_line == err_line and isinstance(status, str) and status.startswith("Hoàn thành") and not exclude_user and not temp_revert:
                                   items_to_revert_indices_snapshot.append(i); reverted_lines.add(item_line)
                    if not items_to_revert_indices_snapshot:
                         print(f"Could not identify item on line {err_line} to revert. Stopping verification.")
                         self.after(0, self.update_status, f"Không tìm thấy mục dịch trên dòng lỗi {err_line}.")
                         self.after(0, lambda: Messagebox.show_warning(f"Không thể tự sửa lỗi cú pháp gần dòng {err_line}.\nFile sẽ được lưu với lỗi.", "Lỗi Cú pháp", parent=self))
                         break
                    for index in items_to_revert_indices_snapshot:
                        current_data_snapshot[index][7] = True
                        current_data_snapshot[index][2] = f"Hoàn nguyên (Lỗi dòng {err_line})"
                        reverted_in_this_pass += 1
                    reverted_count_total += reverted_in_this_pass; print(f"Marked {reverted_in_this_pass} item(s) on line {err_line} for revert.")
                except Exception as e_parse:
                    print(f"Unexpected error during syntax verification: {e_parse}"); traceback.print_exc()
                    self.after(0, self.update_status, f"Lỗi kiểm tra cú pháp: {e_parse}"); parse_successful = False; break

            save_status_prefix = "Đã lưu"
            if VERIFY_SYNTAX:
                if parse_successful: save_status_prefix = f"Đã lưu (tự sửa {reverted_count_total} lỗi)" if reverted_count_total > 0 else "Đã lưu (cú pháp OK)"
                else: save_status_prefix = "Đã lưu (CÓ LỖI CÚ PHÁP!)"
            self.after(0, self.update_status, f"Đang ghi vào file: {save_path.name}...")
            with open(save_path, 'w', encoding='utf-8') as f: f.writelines(final_output_lines)

            if reverted_count_total > 0:
                 print(f"Updating main data/UI for {reverted_count_total} reverted items...")
                 item_id_to_index_map = {data[4]: i for i, data in enumerate(self.translation_data) if len(data) >= 5}
                 for snapshot_item in current_data_snapshot:
                      if len(snapshot_item) >= 8 and snapshot_item[7]:
                           item_id = snapshot_item[4]; original_index = item_id_to_index_map.get(item_id)
                           if original_index is not None and original_index < len(self.translation_data):
                                main_data_item = self.translation_data[original_index]
                                if len(main_data_item) >= 7:
                                     revert_msg = snapshot_item[2]
                                     main_data_item[2] = revert_msg
                                     self.after(0, self._update_tree_item_display, original_index)

            msg = f"{save_status_prefix} ({final_replacements} dịch / {final_items_processed} mục) vào: {save_path}"
            self.after(0, self.update_status, msg)
            info_title = "Lưu thành công" + (" (với lỗi cú pháp)" if not parse_successful and VERIFY_SYNTAX else "")

            user_skipped_count = 0; filter_comment_skipped_count = 0; other_skipped_count = 0
            for item in self.translation_data:
                if len(item) >= 7 and item[5]:
                     status = str(item[2])
                     if status == "Bỏ qua (Người dùng)": user_skipped_count += 1
                     elif status == "Bỏ qua (Lọc #)" or status == "Nghi ngờ (Lọc #)": filter_comment_skipped_count += 1
                     elif status == "Bỏ qua (f-string)" or status == "Rỗng/Whitespace": other_skipped_count += 1

            info_msg = f"{save_status_prefix}!\n({final_replacements} dịch / {final_items_processed} mục đã xử lý)\n"
            if user_skipped_count > 0: info_msg += f"({user_skipped_count} mục được người dùng bỏ qua)\n"
            if filter_comment_skipped_count > 0: info_msg += f"({filter_comment_skipped_count} comment bị lọc bỏ qua)\n"
            if other_skipped_count > 0: info_msg += f"({other_skipped_count} mục rỗng/f-string bị bỏ qua)\n"
            if reverted_count_total > 0: info_msg += f"({reverted_count_total} mục đã hoàn nguyên do lỗi cú pháp trên dòng: {', '.join(map(str, sorted(list(reverted_lines))))})\n"
            info_msg += f"\n{save_path}"
            self.after(0, lambda: Messagebox.show_info(info_msg, info_title, parent=self))


        except Exception as e:
             print(f"Error saving translated file: {e}"); traceback.print_exc()
             self.after(0, self.update_status, f"Lỗi nghiêm trọng khi lưu file dịch: {e}")

    def load_settings(self):
        try:
            if os.path.exists(CONFIG_FILE):
                with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                    loaded = json.load(f); settings = DEFAULT_SETTINGS.copy(); settings.update(loaded)
                    for key, value in DEFAULT_SETTINGS.items():
                         if key not in settings: settings[key] = value
                    settings["font_size"] = max(8, int(settings.get("font_size", DEFAULT_SETTINGS["font_size"])))
                    settings["batch_size"] = max(1, int(settings.get("batch_size", DEFAULT_SETTINGS["batch_size"])))
                    settings["rpm_limit"] = max(1, int(settings.get("rpm_limit", DEFAULT_SETTINGS["rpm_limit"])))
                    settings["max_batch_retries"] = max(0, int(settings.get("max_batch_retries", DEFAULT_SETTINGS["max_batch_retries"])))
                    settings["max_item_retries"] = max(0, int(settings.get("max_item_retries", DEFAULT_SETTINGS["max_item_retries"])))
                    settings["retry_delay_seconds"] = max(1, int(settings.get("retry_delay_seconds", DEFAULT_SETTINGS["retry_delay_seconds"])))
                    if settings.get("string_translation_mode") not in ["none", "safe_ast", "all"]: settings["string_translation_mode"] = DEFAULT_SETTINGS["string_translation_mode"]
                    settings["verify_syntax_after_save"] = bool(settings.get("verify_syntax_after_save", DEFAULT_SETTINGS["verify_syntax_after_save"]))
                    settings["max_verification_attempts"] = max(1, int(settings.get("max_verification_attempts", DEFAULT_SETTINGS["max_verification_attempts"])))
                    settings["use_gemini_scan"] = bool(settings.get("use_gemini_scan", DEFAULT_SETTINGS["use_gemini_scan"]))
                    return settings
            return DEFAULT_SETTINGS.copy()
        except Exception as e:
            print(f"Error loading settings '{CONFIG_FILE}': {e}. Using defaults.")
            return DEFAULT_SETTINGS.copy()

    def save_settings(self):
        try:
            settings_to_save = self.settings.copy()
            settings_to_save["font_size"] = int(settings_to_save.get("font_size", DEFAULT_SETTINGS["font_size"]))
            settings_to_save["batch_size"] = int(settings_to_save.get("batch_size", DEFAULT_SETTINGS["batch_size"]))
            settings_to_save["rpm_limit"] = int(settings_to_save.get("rpm_limit", DEFAULT_SETTINGS["rpm_limit"]))
            settings_to_save["max_batch_retries"] = int(settings_to_save.get("max_batch_retries", DEFAULT_SETTINGS["max_batch_retries"]))
            settings_to_save["max_item_retries"] = int(settings_to_save.get("max_item_retries", DEFAULT_SETTINGS["max_item_retries"]))
            settings_to_save["retry_delay_seconds"] = int(settings_to_save.get("retry_delay_seconds", DEFAULT_SETTINGS["retry_delay_seconds"]))
            settings_to_save["max_verification_attempts"] = int(settings_to_save.get("max_verification_attempts", DEFAULT_SETTINGS["max_verification_attempts"]))
            if settings_to_save.get("string_translation_mode") not in ["none", "safe_ast", "all"]: settings_to_save["string_translation_mode"] = DEFAULT_SETTINGS["string_translation_mode"]
            settings_to_save["verify_syntax_after_save"] = bool(settings_to_save.get("verify_syntax_after_save", DEFAULT_SETTINGS["verify_syntax_after_save"]))
            settings_to_save["use_gemini_scan"] = bool(settings_to_save.get("use_gemini_scan", DEFAULT_SETTINGS["use_gemini_scan"]))
            with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
                json.dump(settings_to_save, f, indent=4)
            print(f"Settings saved to {CONFIG_FILE}")
        except Exception as e:
            print(f"Error saving settings: {e}")
            if self.winfo_exists(): Messagebox.show_error(f"Không thể lưu cài đặt:\n{e}", "Lỗi Lưu Cài đặt", parent=self)


if __name__ == "__main__":
    app = None
    try:
         try: from ctypes import windll; windll.shcore.SetProcessDpiAwareness(1)
         except: pass
         app = PythonTranslatorApp()
         app.mainloop()
    except tk.TclError as e:
         if "theme" in str(e).lower() and "not found" in str(e).lower():
              print(f"Theme Error: {e}. Falling back.");
              try:
                  temp_root = tk.Tk(); temp_root.withdraw()
                  try:
                      class MinimalAppForSettings: load_settings = PythonTranslatorApp.load_settings
                      dummy_app = MinimalAppForSettings()
                      sets = dummy_app.load_settings()
                  except Exception as load_err:
                      print(f"Could not load settings during fallback: {load_err}")
                      sets = DEFAULT_SETTINGS.copy()
                  theme_name = str(e).split("'")[1] if "'" in str(e) else "unknown"
                  sets["theme"]="litera";
                  try:
                      with open(CONFIG_FILE,'w',encoding='utf-8') as f: json.dump(sets,f,indent=4)
                      print("Saved fallback theme. Restart needed.")
                      messagebox.showinfo("Lỗi Theme", f"Theme '{theme_name}' lỗi. Đặt lại thành 'litera'.\nVui lòng khởi động lại.", parent=temp_root)
                  except Exception as e_save:
                      print(f"Cannot save fallback: {e_save}");
                      messagebox.showerror("Lỗi Theme", f"Theme '{theme_name}' lỗi, không lưu được fallback.\n{e}", parent=temp_root)
                  temp_root.destroy()
              except Exception as e_fb: print(f"CRITICAL Fallback Error: {e_fb}")
         else: print(f"Unhandled TclError: {e}"); traceback.print_exc(); messagebox.showerror("Lỗi Tcl/Tk", f"Đã xảy ra lỗi Tcl/Tk không mong muốn:\n{e}")
    except Exception as e_startup: print(f"Critical startup error: {e_startup}"); traceback.print_exc(); messagebox.showerror("Lỗi Khởi động", f"Đã xảy ra lỗi nghiêm trọng khi khởi động:\n{e_startup}")

