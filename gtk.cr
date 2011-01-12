module gtk;

c_include "gtk/gtk.h";

import std.string;

alias gtcis = g_type_check_instance_cast;

// TODO: multi-alias template support for this

GtkContainer* gtkCastContainer(GtkWidget* gw) {
  return GtkContainer*: gtcis (GTypeInstance*:gw, gtk_container_get_type());
}

GtkWindow* gtkCastWindow(GtkWidget* gw) {
  return GtkWindow*: gtcis (GTypeInstance*:gw, gtk_window_get_type());
}

GtkButton* gtkCastButton(GtkWidget* gw) {
  return GtkButton*: gtcis (GTypeInstance*:gw, gtk_button_get_type());
}

GtkButton* gtkCastBox(GtkWidget* gw) {
  return GtkButton*: gtcis (GTypeInstance*:gw, gtk_box_get_type());
}

GtkScrolledWindow* gtkCastScrolledWindow(GtkWidget* gw) {
  return GtkScrolledWindow*: gtcis (GTypeInstance*:gw, gtk_scrolled_window_get_type());
}

GtkTreeView* gtkCastTreeView(GtkWidget* gw) {
  return GtkTreeView*: gtcis (GTypeInstance*:gw, gtk_tree_view_get_type());
}

GtkTreeView* gtkCastTreeModel(GtkWidget* gw) {
  return GtkTreeView*: gtcis (GTypeInstance*:gw, gtk_tree_model_get_type());
}

extern(C) size_t g_signal_connect_data (gpointer instance, char*, void*, void*, void*, GConnectFlags);

// turn function-pointer(void*) type callbacks into delegate callbacks
(void*, void*)[~] store;

template call-dg(T) <<EOF
  ReturnType T call-dg (ParamTypes T p, void* data) {
    alias ret = ReturnType T;
    auto dg = * ret delegate(ParamTypes T)*: data;
    auto res = dg p;
    return res;
  }
EOF

template g_signal_connect(T) <<EOF
  // void g_signal_connect (GtkWidget* w, string s, void delegate(GtkWidget*) dg) {
  void g_signal_connect (T t) {
    store ~= (void*, void*): t[2];
    auto dgvalue = &(call-dg!type-of t[2]);
    g_signal_connect_data (gpointer: t[0], toStringz(t[1]), void*: dgvalue, &store[store.length - 1], null, 0);
  }
EOF
