#include <smoke.h>
#include <smoke/qtgui_smoke.h>
#include <smoke/qtcore_smoke.h>
 
#include <iostream>
#include <QtCore/QString>
#include <QtCore/QObject>
#include <string>
#include <vector>
#include <stdio.h>

#define ALIGNED __attribute__ ((force_align_arg_pointer))
#define LET(A, B) typeof(B) A = (B)
#define EXPORT extern "C" ALIGNED

using namespace std;

/*
 * This class will intercept all virtual method calls and will get
 * notified when an instance created by smoke gets destroyed.
 */
class MySmokeBinding : public SmokeBinding
{
public:
  MySmokeBinding(Smoke *s) : SmokeBinding(s) {}
 
  void deleted(Smoke::Index classId, void *obj) {
    printf("~%s (%p)\n", className(classId), obj);
  }
 
  bool callMethod(Smoke::Index method, void *obj,
    Smoke::Stack args, bool isAbstract)
  {
    Smoke::Method meth = smoke->methods[method];
    string name;
    
    // check for method flags
    if (meth.flags & Smoke::mf_protected) name += "protected ";
    if (meth.flags & Smoke::mf_const) name += "const ";

    // add the name
    name += smoke->methodNames[meth.name] + string("(");

    // iterate over the argument list and build up the
    // parameter names
    Smoke::Index *idx = smoke->argumentList + meth.args;
    while (*idx) {
      name += smoke->types[*idx].name;
      idx++;
      if (*idx) name += ", ";
    }
    name += ")";
    if (name == "x11EventFilter(_XEvent*)") {
      return false;
    }
    if (name == "setVisible(bool)") {
      return false;
    }
    // cout << "huh - " << name << endl;
    if (name == "protected mousePressEvent(QMouseEvent*)")
      cout << className(meth.classId) << "(" << obj
            << ")::" << name << endl;
    return false;
  }

  /*
    * In a bindings runtime, this should return the classname as used
    * in the bindings language, e.g. Qt::Widget in Ruby or
    * Qyoto.QWidget in C#
    */
  char *className(Smoke::Index classId) {
    return (char*) smoke->classes[classId].className;
  }
};

enum Library {
  QTGui
};

EXPORT void qt_init() {
  init_qtcore_Smoke();
  init_qtgui_Smoke();
}

EXPORT void qt_fini() {
  delete qtgui_Smoke;
  delete qtcore_Smoke;
}

EXPORT void* alloc_binding(Library lib) {
  switch (lib) {
    case QTGui: return new MySmokeBinding(qtgui_Smoke);
    default: return NULL;
  }
}

struct MyMethod {
  Smoke::Class *myClass;
  Smoke::Method *myMethod;
};

struct MyInvocation {
  vector<Smoke::StackItem> stack;
};

EXPORT void *alloc_string(char *str, int len) {
  QString *qs = new QString(QString::fromUtf8(str, len));
  return (void*) qs;
}

EXPORT void *lookup_class_method(char *classname, char *methodname) {
  Smoke::ModuleIndex methodId = qtgui_Smoke->findMethod(classname, methodname);
  if (methodId.smoke == NULL) return NULL;
  if (methodId.index <= 0) { printf("Ambiguous lookup: %s in %s\n", methodname, classname); return NULL; }
  MyMethod *res = new MyMethod;
  res->myClass = &methodId.smoke->classes[methodId.smoke->methodMaps[methodId.index].classId];
  res->myMethod = &methodId.smoke->methods[methodId.smoke->methodMaps[methodId.index].method];
  return (void*) res;
}

EXPORT void *stack_add_voidptr(void *prev, void *value) {
  MyInvocation* minv = (MyInvocation*) prev;
  if (minv == NULL) minv = new MyInvocation;
  Smoke::StackItem item;
  item.s_voidp = value;
  minv->stack.push_back(item);
  return (void*) minv;
}

EXPORT void *call_method(void *method, void *object, void *stack) {
  MyMethod* meth = (MyMethod*) method;
  MyInvocation* inv = (MyInvocation*) stack;
  // printf("call %s on %p: %s\n", qtgui_Smoke->methodNames[meth->myMethod->name], object, meth->myClass->className);
  (*meth->myClass->classFn)(meth->myMethod->method, object, &inv->stack[0]);
  void *res = inv->stack[0].s_voidp;
  delete inv;
  delete meth;
  // printf("  => %p\n", res);
  return res;
}

EXPORT void *make_binding(char *classid, void *object, void *stack) {
  Smoke::ModuleIndex classId = qtgui_Smoke->findClass(classid);
  MyInvocation* inv = (MyInvocation*) stack;
  // printf("set binding for %s on %p\n", classId.smoke->classes[classId.index].className, object);
  (*classId.smoke->classes[classId.index].classFn)(0, object, &inv->stack[0]);
  void *res = inv->stack[0].s_voidp;
  delete inv;
  return res;
}
