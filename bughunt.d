// isolate errors in the peephole optimizer
module bughunt;

import qd, SDL_ttf, tools.base, tools.compat, tools.time, tools.threadpool, tools.mersenne, tools.functional;

extern(C) {
  int pipe(int*);
  int close(int);
  void exit(int);
}

string readStream(InputStream IS) {
  string res;
  ubyte[512] buffer;
  int i;
  do {
    i = IS.read(buffer);
    if (i < 0) throw new Exception(Format("Read error: ", i));
    res ~= cast(string) buffer[0 .. i];
  } while (i);
  return res;
}

string readback(string cmd) {
  int[2] fd; // read end, write end
  if (-1 == pipe(fd.ptr)) throw new Exception(Format("Can't open pipe! "));
  scope(exit) close(fd[0]);
  auto cmdstr = Format(cmd, " >&", fd[1], " &");
  system(toStringz(cmdstr));
  close(fd[1]);
  scope fs = new CFile(fdopen(fd[0], "r"), FileMode.In);
  return readStream(fs);
}

enum State {
  On, Testing, KnownGood
}

int main(string[] args) {
  auto exec = args.take();
  if (args.length != 1) {
    writefln(exec, " \"fcc params\"");
    return 1;
  }
  auto info = readback("fcc -config-opts \"info\" "~args[0]~" -o bughunt_test").split("\n");
  void build(string flags) {
    auto line = Format("fcc -config-opts \""~flags~"\" "~args[0]~" -o bughunt_test >/dev/null");
    logln("> ", line);
    system(toStringz(line));
  }
  string[] names;
  writefln("info: ", info);
  foreach (line; info)
    if (auto rest = line.startsWith("id:"))
      names ~= line.between("name:", " ");
  auto states = new State[names.length];
  
  int[] left;
  foreach (i, name; names) left ~= i;
  
  auto rowheight = 10;
  void delegate() maindg;
  auto tp = new Threadpool(1), mainpool = new Threadpool(0);
  void render() {
    auto offs = 24;
    foreach (i, state; states) {
      auto color = (state == State.On) ? Green : ((state == State.Testing) ? Yellow : Red);
      circle(32, offs, rowheight / 3, White, Fill=color);
      print(48, offs, names[i], Center|Right);
      offs += rowheight;
    }
  }
  void update() { mainpool.future({ render; }).eval; }
  
  string genFlags() {
    string res;
    foreach (i, state; states) if (state != State.On) {
      if (res) res ~= ",";
      res ~= Format("disable ", i);
    }
    return res;
  }
  // does it work with that range knocked out?
  bool works() {
    update;
    build(genFlags());
    int res = system("./bughunt_test");
    bool itWorked = res == 0;
    /*
    auto dialog = display.select(300, 20, 150, 40);
    
    bool forb, res;
    synchronized(SyncObj!(maindg)) maindg = {
      line(dialog.tl, dialog.br, Box=White, Fill=Black);
      print(dialog, "Did it work?", Top);
      print(dialog, "Yes", Left|Bottom);
      print(dialog, "No", Right|Bottom);
      if (mouse in dialog && mouse.clicked) {
        res = mouse.pos.x < (dialog.tl.x + dialog.br.x) / 2;
        synchronized(SyncObj!(maindg)) maindg = null;
        cls;
        forb = true;
      }
    };
    while (!forb) slowyield; // idlespin lol
    logln("You clicked ", res?"Yes":"No", ".");
    return res;*/
    logln("Code ", res, ": ", itWorked?"Success":"Failure");
    return itWorked;
  }
  float threshold = 0.5;
  int bisect() {
    while (true) {
      logln("threshold: ", threshold);
      for (int i = 0; i < left.length; ++i) {
        states[left[i]] = ((rand() * 1f / typeof(rand()).max) < threshold)  ? State.On : State.Testing;
      }
      if (works) { threshold = (threshold + 1) / 2; continue; }
      else {
        threshold = threshold * 0.8;
        for (int i = 0; i < left.length; ++i) {
          if (states[left[i]] == State.On) continue;
          else {
            states[left[i]] = State.KnownGood;
          }
        }
      }
      {
        auto newleft = left.dup[0 .. 0];
        for (int i = 0; i < left.length; ++i) {
          if (states[left[i]] == State.KnownGood) continue;
          else newleft ~= left[i];
        }
        left = newleft;
      }
    }
    logln("required to fail: ", left /map/ ex!("a -> b -> a[b]")(names));
    return 0;
  }
  
  screen(640, 24 + rowheight * names.length);
  render;
  tp.addTask({
    bisect();
  });
  while (true) {
    synchronized(SyncObj!(maindg)) if (maindg) maindg();
    mainpool.idle();
    flip;
    events;
  }
  return 0;
}
