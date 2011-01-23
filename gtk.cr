module gtk;

c_include "gtk/gtk.h";

import std.string;

alias gtcic = g_type_check_instance_cast;

// TODO: multi-alias template support for this

GtkContainer* gtkCastContainer(GtkWidget* gw) {
  return GtkContainer*: gtcic (GTypeInstance*:gw, gtk_container_get_type());
}

GtkWindow* gtkCastWindow(GtkWidget* gw) {
  return GtkWindow*: gtcic (GTypeInstance*:gw, gtk_window_get_type());
}

GtkButton* gtkCastButton(GtkWidget* gw) {
  return GtkButton*: gtcic (GTypeInstance*:gw, gtk_button_get_type());
}

alias G_TYPE_FUNDAMENTAL_SHIFT = 2;

GtkObject* gtkCastObject(GtkWidget* gw) {
  return GtkObject*: gtcic (GTypeInstance*:gw, GType: (20 << G_TYPE_FUNDAMENTAL_SHIFT));
}

GtkBox* gtkCastBox(GtkWidget* gw) {
  return GtkButton*: gtcic (GTypeInstance*:gw, gtk_box_get_type());
}

GtkScrolledWindow* gtkCastScrolledWindow(GtkWidget* gw) {
  return GtkScrolledWindow*: gtcic (GTypeInstance*:gw, gtk_scrolled_window_get_type());
}

GtkTextView* gtkCastTextView(GtkWidget* gw) {
  return GtkTextView*: gtcic (GTypeInstance*:gw, gtk_text_view_get_type());
}

GtkTreeView* gtkCastTreeView(GtkWidget* gw) {
  return GtkTreeView*: gtcic (GTypeInstance*:gw, gtk_tree_view_get_type());
}

GtkTreeView* gtkCastTreeModel(GtkWidget* gw) {
  return GtkTreeView*: gtcic (GTypeInstance*:gw, gtk_tree_model_get_type());
}

GtkEntry* gtkCastEntry(GtkWidget* gw) {
  return GtkEntry*: gtcic (GTypeInstance*:gw, gtk_entry_get_type());
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
  // void g_signal_connect (GtkObject* w, string s, void delegate(GtkObject*) dg) {
  void g_signal_connect (T t) {
    store ~= (void*, void*): t[2];
    auto dgvalue = &(call-dg!type-of t[2]);
    g_signal_connect_data (gpointer: t[0], toStringz(t[1]), void*: dgvalue, &store[store.length - 1], null, 0);
  }
EOF

RenameIdentifier gtk_hbox_new _gtk_hbox_new;
GtkWidget* gtk_hbox_new(gboolean homogenous = false, gint spacing = 0) return _gtk_hbox_new(homogenous, spacing);

RenameIdentifier gtk_vbox_new _gtk_vbox_new;
GtkWidget* gtk_vbox_new(gboolean homogenous = false, gint spacing = 0) return _gtk_vbox_new(homogenous, spacing);

RenameIdentifier gtk_box_pack_start _gtk_box_pack_start;
void gtk_box_pack_start(GtkBox* box, GtkWidget* child, gboolean expand = false, gboolean fill = false, guint padding = 0)
  return _gtk_box_pack_start (box, child, expand, fill, padding);

RenameIdentifier gtk_box_pack_end _gtk_box_pack_end;
void gtk_box_pack_end(GtkBox* box, GtkWidget* child, gboolean expand = false, gboolean fill = false, guint padding = 0)
  return _gtk_box_pack_end (box, child, expand, fill, padding);
