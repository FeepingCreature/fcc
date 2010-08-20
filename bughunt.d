// isolate errors in the peephole optimizer
module bughunt;

import qd, SDL_ttf, tools.base, tools.compat, tools.time;

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
  On, Testing, KnownBad
}

int main(string[] args) {
  auto exec = args.take();
  if (args.length != 1) {
    writefln(exec, " \"fcc params\"");
    return 1;
  }
  auto info = readback("./fcc -config-opts \"info\" "~args[0]~" -o bughunt_test").split("\n");
  void build(string flags) {
    auto line = Format("./fcc -config-opts \""~flags~"\" "~args[0]~" -o bughunt_test");
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
  
  auto rowheight = 20;
  void render() {
    auto offs = 24;
    foreach (i, state; states) {
      auto color = (state == State.On) ? Green : ((state == State.Testing) ? Yellow : Red);
      circle(32, offs, rowheight / 3, White, Fill=color);
      print(48, offs, names[i], Center|Right);
      offs += rowheight;
    }
  }
  void update() { render; flip; events; }
  
  void setupTest(int from, int to, bool undo) {
    for (int i = from; i < to; ++i) {
      states[left[i]] = undo?State.On:State.Testing;
    }
  }
  string genFlags() {
    string res;
    foreach (i, state; states) if (state != State.On) {
      if (res) res ~= ",";
      res ~= Format("disable ", i);
    }
    return res;
  }
  // does it work with that range knocked out?
  bool works(int from, int to) {
    setupTest(from, to, false);
    build(genFlags());
    system("./bughunt_test");
    setupTest(from, to, true);
    for (int i = 0; i < 50; ++i) { sleep(0.1); flip; events; }
    while (true) {
      writefln("Did it work? Y/N");
      auto line = readln().chomp();
      if (line == "Y") return true;
      if (line == "N") return false;
    }
  }
  int bisect() {
    int from = 0, to = left.length;
    while (from != to) {
      update;
      auto pivot = from + (to - from) / 2;
      if (works(0, pivot)) {
        to = pivot;
      } else {
        assert(works(0, to));
        from = pivot;
      }
    }
    logln("required ", names[from]);
    exit(1);
    return 0;
  }
  
  screen(640, 24 + rowheight * names.length);
  render;
  bisect();
  while (true) { flip; events; }
  return 0;
}
