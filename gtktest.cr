// ./fcc $(pkg-config --libs --cflags gtk+-2.0) gtktest.cr std/string.cr
module gtktest;

c_include "gtk/gtk.h";

import sys, std.string, std.file;

extern(C) size_t g_signal_connect_data (gpointer instance, char*, void*, void*, void*, GConnectFlags);

GtkContainer* gtkCastContainer(GtkWidget* gw) {
  return g_type_check_instance_cast (gw, gtk_container_get_type());
}

GtkWindow* gtkCastWindow(GtkWidget* gw) {
  return g_type_check_instance_cast (gw, gtk_window_get_type());
}

GtkButton* gtkCastButton(GtkWidget* gw) {
  return g_type_check_instance_cast (gw, gtk_button_get_type());
}

GtkButton* gtkCastBox(GtkWidget* gw) {
  return g_type_check_instance_cast (gw, gtk_box_get_type());
}

GtkScrolledWindow* gtkCastScrolledWindow(GtkWidget* gw) {
  return g_type_check_instance_cast (gw, gtk_scrolled_window_get_type());
}

GtkTreeView* gtkCastTreeView(GtkWidget* gw) {
  return g_type_check_instance_cast (gw, gtk_tree_view_get_type());
}

GtkTreeView* gtkCastTreeModel(GtkWidget* gw) {
  return g_type_check_instance_cast (gw, gtk_tree_model_get_type());
}

(void*, void*)[~] store;

template call-dg(T) <<EOF
  ReturnType T call-dg (ParamTypes T p, void* data) {
    alias ret = ReturnType T;
    auto dg = *ret delegate(ParamTypes T)*:data;
    auto res = dg p;
    return res;
  }
EOF

template g_signal_connect(T) <<EOF
  // void g_signal_connect (GtkWidget* w, string s, void delegate(GtkWidget*) dg) {
  void g_signal_connect (T t) {
    store ~= (void*, void*): t[2];
    auto dgvalue = &(call-dg!typeof(t[2]));
    g_signal_connect_data (t[0], toStringz(t[1]), void*:dgvalue, &store[store.length - 1], null, 0);
  }
EOF

bool delete_event(void* widget, void* event, gpointer data) {
    /* If you return FALSE in the "delete-event" signal handler,
     * GTK will emit the "destroy" signal. Returning TRUE means
     * you don't want the window to be destroyed.
     * This is useful for popping up 'are you sure you want to quit?'
     * type dialogs. */

    g_print ("delete event occurred\n");

    /* Change TRUE to FALSE and the main window will be destroyed with
     * a "delete-event". */

    return true;
}

alias G_TYPE_STRING = GType:(16 << 2);

extern(C) FILE* stdout;
int main (int argc, char **argv) {
    /* This is called in all GTK applications. Arguments are parsed
     * from the command line and are returned to the application. */
    gtk_init (&argc, &argv);
    
    /* create a new window */
    auto window = gtk_window_new (GTK_WINDOW_TOPLEVEL);
    
    gtk_window_set_title(gtkCastWindow(window), "Hello Buttons!");
    
    auto model = gtk_tree_store_new (2, G_TYPE_STRING, G_TYPE_STRING);
    
    string line;
    GtkTreeIter[auto~] iters;
    GtkTreeIter* current() { return &iters[iters.length-1]; }
    GtkTreeIter* prev() { return &iters[iters.length-2]; }
    bool reading;
    writeln "Building model. ";
    while line <- splitAt("\n",
        [for chunk <- readfile open "xmldump.txt": (string: chunk)]) {
      // writeln "> $line";
      if (startsWith(line, "----module ")) {
        auto restp = toStringz line["----module ".length .. line.length];
        GtkTreeIter iter;
        iters ~= iter;
        gtk_tree_store_append (model, current(), null);
        gtk_tree_store_set (model, current(), 0, restp, 1, null, -1);
        int st = (current().stamp);
        reading = true;
      }
      if (startsWith(line, "----done")) {
        iters = typeof(iters):iters[0 .. iters.length-1];
        reading = false;
      }
      if (reading) {
        alias xmlstart = "<node";
        if (startsWith(line, xmlstart)) {
          auto classnamep = toStringz between(line, " classname=\"", "\"");
          auto namep = toStringz between(line, " name=\"", "\"");
          auto infop = toStringz between(line, " info=\"", "\"");
          if (find(line, " info=") == -1) infop = namep;
          GtkTreeIter iter;
          iters ~= iter;
          gtk_tree_store_append (model, current(), prev());
          gtk_tree_store_set (model, current(), 0, classnamep, 1, infop, -1);
        }
        if (line == "</node>") {
          iters = typeof(iters):iters[0 .. iters.length-1];
        }
      }
    }
    
    auto sw = gtk_scrolled_window_new (null, null);
    gtk_scrolled_window_set_policy (
      gtkCastScrolledWindow(sw), 
      GTK_POLICY_AUTOMATIC x 2
    );
    
    auto tree = gtk_tree_view_new ();
    gtk_tree_view_set_headers_visible (gtkCastTreeView(tree), true);
    
    gtk_container_add (gtkCastContainer(sw), tree);
    gtk_container_add (gtkCastContainer(window), sw);
    
    {
      auto renderer = gtk_cell_renderer_text_new ();
      auto column = gtk_tree_view_column_new_with_attributes ("Class",
                      renderer, "text".ptr, 0, null);
      gtk_tree_view_append_column (gtkCastTreeView (tree), column);
      column = gtk_tree_view_column_new_with_attributes ("Info",
                      renderer, "text".ptr, 1, null);
      gtk_tree_view_append_column (gtkCastTreeView (tree), column);
      gtk_tree_view_set_model (gtkCastTreeView (tree), gtkCastTreeModel (model));
      g_object_unref (model);
    }
    
    g_signal_connect_data (
      window, "delete-event",
      void*:function bool(void* widget, event, data) { return false; },
      null, null, 0
    );
    
    g_signal_connect (window, "destroy", delegate void(GtkWidget*) { gtk_main_quit(); });
    
    gtk_container_set_border_width (gtkCastContainer(window), 10);
    
    gtk_widget_show_all (window);
    
    /* All GTK applications must have a gtk_main(). Control ends here
     * and waits for an event to occur (like a key press or
     * mouse event). */
    gtk_main ();
    
    return 0;
}
