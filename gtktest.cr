// ./fcc $(pkg-config --libs --cflags gtk+-2.0) gtktest.cr std/string.cr
module gtktest;

c_include "gtk/gtk.h";

import sys, std.string;

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

int main (int argc, char **argv) {
    /* This is called in all GTK applications. Arguments are parsed
     * from the command line and are returned to the application. */
    gtk_init (&argc, &argv);
    
    /* create a new window */
    auto window = gtk_window_new (GTK_WINDOW_TOPLEVEL);
    
    gtk_window_set_title(gtkCastWindow(window), "Hello Buttons!");
    
    /* When the window is given the "delete-event" signal (this is given
     * by the window manager, usually by the "close" option, or on the
     * titlebar), we ask it to call the delete_event () function
     * as defined above. The data passed to the callback
     * function is NULL and is ignored in the callback function. */
    g_signal_connect_data (window, "delete-event", void*:function bool(void* widget, event, data) { return false; }, null, null, 0);
    
    /* Here we connect the "destroy" event to a signal handler.  
     * This event occurs when we call gtk_widget_destroy() on the window,
     * or if we return FALSE in the "delete-event" callback. */
    g_signal_connect (window, "destroy", delegate void(GtkWidget*) { gtk_main_quit(); });
    
    // #define _G_TYPE_CIC(ip,gt,ct) ((ct*) g_type_check_instance_cast ((GTypeInstance*) ip, gt))
    /* Sets the border width of the window. */
    gtk_container_set_border_width (gtkCastContainer(window), 10);
    
    auto box1 = gtk_hbox_new(false, 0);
    
    gtk_container_add(gtkCastContainer(window), box1);
    {
      auto button = gtk_button_new_with_label ("Button 1");
      g_signal_connect (button, "clicked", delegate void(GtkWidget* widget) { g_print "Hello World button1\n"; });
      gtk_box_pack_start (gtkCastBox(box1), button, true, true, 0);
      gtk_widget_show (button);
    }
    
    {
      auto button = gtk_button_new_with_label ("Button 2");
      g_signal_connect (button, "clicked", delegate void(GtkWidget* widget) { g_print "Hello World button2\n"; });
      gtk_box_pack_start (gtkCastBox(box1), button, true, true, 0);
      gtk_widget_show (button);
    }
    
    gtk_widget_show (box1);
    
    /* and the window */
    gtk_widget_show (window);
    
    /* All GTK applications must have a gtk_main(). Control ends here
     * and waits for an event to occur (like a key press or
     * mouse event). */
    gtk_main ();
    
    return 0;
}
