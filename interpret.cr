module interpret;

import std.file, std.string, std.stream, std.thread, std.time;

import std.c.stdio, std.c.string;

extern(C) FILE* stdin;

string chomp(string s) {
  while (s.length && s[$ - 1] == "\n"[0])
    s = s[0 .. $-1];
  while (s.length && s[$ - 1] == "\r"[0])
    s = s[0 .. $-1];
  return s;
}

class Exception {
  string text;
  void init(string s) { text = s; }
}

class AcceptException : Exception { }
class EvalException : Exception { }

void mustAccept(string* sp, string m) {
  alias s = *sp;
  if !s.startsWith m {
    raise-error new AcceptException "Expected '$m' at '$s'!";
  }
  s = s[m.length .. $].strip();
}

bool isNum(int i) {
  if (i < int:("0"[0])) return false;
  if (i > int:("9"[0])) return false;
  return true;
}

int eval-expr(string* sp,
  int delegate(int) read-input, read-reg,
  void delegate(int, int) set-output, set-reg) {
  alias s = *sp;
  auto dgs = (read-input, read-reg, set-output, set-reg);
  if !s.length {
    raise-error new EvalException "No input text. ";
  }
  if s[0].isNum() {
    int len = 1;
    while s[len].isNum() len ++;
    (int i, s) = (s[0 .. len].atoi(), s[len .. $]);
    return i;
  }
  if (auto rest = s.startsWith "I[") {
    int idx = eval-expr(&rest, dgs);
    s = rest;
    sp.mustAccept "]";
    return read-input idx;
  }
  if (auto rest = s.startsWith "R[") {
    int idx = eval-expr(&rest, dgs);
    s = rest;
    sp.mustAccept "]";
    return read-reg idx;
  }
  if (auto rest = s.startsWith "LET(") {
    void delegate(int, int) set;
    int which-id;
    if (auto rest2 = rest.startsWith "R[") {
      which-id = eval-expr(&rest2, dgs);
      s = rest2;
      sp.mustAccept "]";
      set = set-reg;
    }
    if (auto rest2 = rest.startsWith "O[") {
      which-id = eval-expr(&rest2, dgs);
      s = rest2;
      sp.mustAccept "]";
      set = set-output;
    }
    if (!set) {
      raise-error new EvalException "Could not match output at $rest. ";
    }
    sp.mustAccept ",";
    auto value = eval-expr(sp, dgs);
    sp.mustAccept ")";
    set(which-id, value);
    return value;
  }
  (bool, int) testinstr(string st, int delegate(int, int) dg) {
    if (auto rest = (*sp).startsWith st) {
      auto val1 = eval-expr(&rest, dgs);
      mustAccept(&rest, ",");
      
      auto val2 = eval-expr(&rest, dgs);
      mustAccept(&rest, ")");
      
      *sp = rest;
      return (true, dg(val1, val2));
    }
    return (false, 0);
  }
  for (auto tuple <- [
    ("AND(", delegate int(int a, b) return a & b; ),
    ("OR(", delegate int(int a, b) return a | b; ),
    ("SHL(", delegate int(int a, b) return a << b; ),
    ("SHR(", delegate int(int a, b) return a >> b; ),
    ("ADD(", delegate int(int a, b) return a + b; ),
    ("MUL(", delegate int(int a, b) return a * b; ),
    ("EQ(", delegate int(int a, b) return eval a == b; ),
    ("GREATER(", delegate int(int a, b) return eval a > b; ),
    ("SMALLER(", delegate int(int a, b) return eval a < b; )
  ]) {
    auto res = testinstr tuple;
    if res[0] return res[1];
  }
  if (auto rest = s.startsWith "NOT(") {
    auto val = eval-expr(&rest, dgs);
    (&rest).mustAccept ")";
    s = rest;
    return ¬val;
  }
  raise-error new EvalException "Could not parse '$s'!";
}

int eval-exprs(string* sp,
  int delegate(int) read-input, read-reg,
  void delegate(int, int) set-output, set-reg) {
  auto dgs = (read-input, read-reg, set-output, set-reg);
  auto res = eval-expr(sp, dgs);
  if (auto rest = (*sp).startsWith "; ") {
    *sp = rest;
    return eval-exprs(sp, dgs);
  }
  return res;
}

import gtk;

extern(C) int printf(char*, ...);

int main (int argc, char** argv) {
  gtk_init (&argc, &argv);
  auto window = gtk_window_new GTK_WINDOW_TOPLEVEL;
  
  g_signal_connect (window.gtkCastObject(), "destroy", delegate void(GtkObject*) { writeln "destroy. "; gtk_main_quit(); });
  
  window.gtkCastContainer().gtk_container_set_border_width 10;
  
  GtkWidget* full_box, inputs_box, outputs_box, regs_box;
  full_box = gtk_hbox_new ();
  (inputs_box, outputs_box, regs_box)
           = gtk_vbox_new() x 3;
  
  GtkEntry*[16] inputs, regs, outputs;
  for (int i <- 0..16) {
    
    GtkLabel* mkLabel(string s) {
      return gtk_label_new toStringz s;
    }
    
    GtkBox* hpack(GtkWidget* a, GtkWidget* b)
      using gtk_hbox_new().gtkCastBox() prefix gtk_box_
    {
      pack_start a;
      pack_end b;
      return that;
    }
    
    using gtk_entry_new().gtkCastEntry() {
      prefix gtk_entry_set_ { width_chars 5; text "0"; }
      inputs[i] = that;
      inputs_box.gtkCastBox().gtk_box_pack_start
        hpack(mkLabel("I$i"), that);
    }
    using gtk_entry_new().gtkCastEntry() {
      prefix gtk_entry_set_ { width_chars 5; text "0"; editable false; }
      outputs[i] = that;
      outputs_box.gtkCastBox().gtk_box_pack_start
        hpack(mkLabel("O$i"), that);
    }
    using gtk_entry_new().gtkCastEntry() {
      prefix gtk_entry_set_ { width_chars 5; text "0"; }
      regs[i] = that;
      regs_box.gtkCastBox().gtk_box_pack_start
        hpack(mkLabel("R$i"), that);
    }
  }
  
  auto main_box = gtk_vbox_new ();
  
  auto tv = gtk_text_view_new ();
  tv.gtkCastTextView().gtk_text_view_set_editable false;
  main_box.gtkCastBox().gtk_box_pack_start (tv, expand => true, fill => true);
  
  auto input_label = gtk_label_new(toStringz "> ");
  auto input_field = gtk_entry_new();
  prefix gtk_box_ {
    auto input_box = gtk_hbox_new ();
    input_box.gtkCastBox().pack_start input_label;
    input_box.gtkCastBox().pack_end (input_field, expand => true, fill => true);
    main_box.gtkCastBox().pack_end input_box;
  }
  
  using full_box.gtkCastBox() prefix gtk_box_ {
    pack_start inputs_box;
    pack_start regs_box;
    pack_end outputs_box;
    pack_start (main_box, expand => true, fill => true);
  }
  
  window.gtkCastContainer().gtk_container_add full_box;
  
  gtk_widget_show_all window;
  
  string[auto~] cache;
  void print-to-buffer(string s) {
    s ~= "\n";
    auto tbuf = tv.gtkCastTextView().gtk_text_view_get_buffer ();
    GtkTextIter end;
    tbuf.gtk_text_buffer_get_end_iter (&end);
    tbuf.gtk_text_buffer_insert (&end, toStringz s, -1);
  }
  void fail(string s) {
    print-to-buffer "! $s";
  }
  auto tp = new ThreadPool;
  string lastExpr;
  auto dgs = (
    delegate int(int i) { return atoi CToString inputs[i].gtk_entry_get_text (); },
    delegate int(int i) { return atoi CToString regs[i].gtk_entry_get_text (); },
    delegate void(int reg, int val) { gtk_entry_set_text (outputs[reg], toStringz "$val"); },
    delegate void(int reg, int val) { gtk_entry_set_text (regs[reg], toStringz "$val"); }
  );
  auto pauseLoops = new Mutex;
  g_signal_connect (input_field.gtkCastObject(), "activate", delegate void(GtkWidget*) {
    auto expr = string:fastdupv void[]:CToString input_field.gtkCastEntry().gtk_entry_get_text();
    // call when input text is accepted, ie. parses
    void accepted() { gtk_entry_set_text(input_field, ""); }
    print-to-buffer "> $expr";
    set-handler (Exception ex) {
      fail(ex.text);
      invoke-exit "return";
    }
    define-exit "return" return;
    if expr == "pause" {
      pauseLoops.lock;
      accepted; return;
    }
    if expr == "resume" {
      pauseLoops.unlock;
      accepted; return;
    }
    if expr == "loop" {
      accepted;
      string copiedLastExpr = lastExpr; // hax
      auto copiedDgs = dgs;
      auto copiedPause = pauseLoops;
      tp.addThread;
      tp.addTask(new delegate void() {
        while true {
          using copiedPause { lock; unlock; }
          string ex2 = copiedLastExpr;
          set-handler (Exception ex) {
            writeln "$(ex.text)";
            invoke-exit "skip";
          }
          bool skip = false;
          define-exit "skip" skip = true; // no "continue" support yet
          if (!skip) eval-exprs(&ex2, copiedDgs);
          sleep 0.01; // wait a sec
        }
      });
      return;
    }
    lastExpr = null;
    auto ex2 = expr;
    auto val = eval-exprs (&ex2,
      read-input => dgs[0],
      read-reg   => dgs[1],
      set-output => dgs[2],
      set-reg    => dgs[3]
    );
    lastExpr = expr;
    accepted;
    print-to-buffer "$val";
  });
  
  gtk_main;
  return 0;
}
