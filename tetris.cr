module tetris;

import sdl; // For graphics output
import std.math, std.file, std.random;

extern(C) int time(int*);

// Board size. size[0] is x is horizontal. size[1] is y is vertical.
alias size = (7, 14);

/*
  The main board. Tracks a field of blocks, together with code to 
  check if a field is free and remove lines (and replace them with
  the lines above).
  Basic housekeeping stuff, nothing special.
*/
class TetrisBoard {
  int[size[0] * size[1]] field;
  void init() { for int i <- 0..field.length field[i] = 0; }
  bool isFree(int x, y) {
    if (x < 0 || y < 0 || x !< size[0] || y !< size[1]) return false;
    return eval field[y * size[0] + x] == 0;
  }
  void set(int x, y, value) { field[y * size[0] + x] = value; }
  int get(int x, y) { return field[y * size[0] + x]; }
  void removeLine(int i) {
    for (int y = i; y > 0; --y) {
      for int x <- 0..size[0] {
        set(x, y, get(x, y-1));
      }
    }
    for int x <- 0..size[0]
      set(x, 0, value => 0);
  }
  void removeFullLines() {
    for int y <- 0..size[1] {
      bool isFull = true;
      for int x <- 0..size[0] {
        if isFree(x, y) isFull = false;
      }
      if (isFull) removeLine(y);
    }
  }
}

// Color 0 == "block is free".
alias Free = 0;

/*
  A Tetris block is implemented as a series of positions on the board,
  and a color.
  vec2i == vector of two integers.
*/
class Block {
  vec2i[] poslist;
  int color;
  void init(int color) { this.color = color; }
  /*
    Try to move the block to a new position on a board.
    First the old block positions are removed.
    Then for every new position: if the block is already in use, 
    restore our old positions and return "false" for "update failed".
    Otherwise fill in the new positions and return true.
  */
  bool tryUpdate(TetrisBoard tb, vec2i[] newlist) {
    // remove old me
    for auto pos <- poslist tb.set(pos.xy, Free);
    void writePos() { for auto pos <- poslist tb.set(pos.xy, color); }
    // check new me
    for auto pos <- newlist if !tb.isFree(pos) { writePos; /* restore */ return false; }
    // commit new me
    poslist = newlist;
    writePos;
    return true;
  }
}

/*
  Rotate a list of coordinates.
  This first finds the bounding box,
  then translates the coordinates so that the middle
  of the bounding box is at 0,
  do a simple rotation around the origin via
    (x, y) = (-y, x)
  and translate back.
*/
void rotate(vec2i[] inp) {
  // find the bounding box of the input coordinates
  vec2i
    tl = vec2i(minlist [for v <- inp: v.x], minlist [for v <- inp: v.y]),
    br = vec2i(maxlist [for v <- inp: v.x], maxlist [for v <- inp: v.y]);
  // function to shift our list by an offset
  void offsetBy(vec2i delta) {
    for int i <- 0..inp.length
      inp[i] += delta;
  }
  
  // the center point
  auto half = (tl + br) / 2;
  
  // make the center point the origin
  offsetBy -half;
  // rotation
  for int i <- 0..inp.length using inp[i]
    (x, y) = (-y, x);
  // and move it back.
  offsetBy half;
  // A little hack to make rotation of the 2x2 box come out right.
  // Even with this, this function still exhibits drift;
  // that is, if you keep rotating a block it will wander to the right.
  // I could fix that by introducing a per-block rotation counter and using that to offset the result
  // but
  // meh.
  offsetBy vec2i(1, 0);
}

// Returns true if the block could be moved down on the board.
bool tryMoveDown(Block bl, TetrisBoard tb) {
  auto list2 = bl.poslist.dup; // Copy the position list
  for int i <- 0..list2.length
    list2[i].y++;
  return bl.tryUpdate(tb, list2); // and try to update the block's list.
}

// Main function! Huzzah!
void main() {
  // give us a good prng .. we could seed this with time(), but a constant is easier to test.
  auto rng = getPRNG 23;
  auto tb = new TetrisBoard;
  // Colours.        Black     Blue            Green,          Aqua            Purple          Yellow          Dark Yellow         Teal
  auto cols = [vec3f(0), vec3f(0, 0, 1), vec3f(0, 1, 0), vec3f(0, 1, 1), vec3f(1, 0, 1), vec3f(1, 1, 0), vec3f(0.5, 0.5, 0), vec3f(0, 0.5, 0.5)];
  // get the screen position for a board position.
  // surf is the sdl.cr default surface.
  vec2i getPos(int x, int y) {
    return vec2i(surf.w *  x / size[0], surf.h * y / size[1]);
  }
  // "Render" our tetris board.
  void draw(TetrisBoard tb) {
    // Cross operator works like this:
    // cross(0..2, 0..3) => [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
    for (int x, int y) <- cross(0..size[0], 0..size[1]) {
      auto col = cols[tb.get(x, y)];
      auto from = getPos(x, y), to = getPos(x+1, y+1);
      // and fill in the box.
      // technically speaking I should be doing int y2, int x2 here for speed reasons
      // (this is very painful on the data cache, because it keeps jumping cache lines)
      // but hell, it's a Tetris. Not exactly high-demand on performance.
      for (int x2, int y2) <- cross(from.x..to.x, from.y..to.y)
        pset(x2, y2, col);
    }
  }
  // Open an SDL window.
  screen (320, 480);
  Block current; // the block currently controlled by the player.
  alias NumBlocks = 7; // number of possible blocks
  // This function tries to spawn a new block at the top.
  bool tryRemakeCurrentBlock() {
    auto kind = rng.rand() % NumBlocks;
    current = new Block(kind + 1); // remember, 0 is "no block". Thus, start with 1.
    vec2i[] blocklist;
    // This is just the position list for each of the basic blocks.
    if (kind == 0) blocklist = [for tup <- [(0, 0), (0, 1), (0, 2), (0, 3)]: vec2i(tup)].eval; // I block
    if (kind == 1) blocklist = [for tup <- [(0, 0), (0, 1), (1, 1), (0, 2)]: vec2i(tup)].eval; // |- block
    if (kind == 2) blocklist = [for tup <- [(0, 0), (0, 1), (0, 2), (1, 2)]: vec2i(tup)].eval; // L block
    if (kind == 3) blocklist = [for tup <- [(1, 0), (1, 1), (1, 2), (0, 2)]: vec2i(tup)].eval; // Reverse L block
    if (kind == 4) blocklist = [for tup <- [(0, 0), (0, 1), (1, 1), (1, 0)]: vec2i(tup)].eval; // Square block
    if (kind == 5) blocklist = [for tup <- [(0, 0), (0, 1), (1, 1), (1, 2)]: vec2i(tup)].eval; // Inverse Z block
    if (kind == 6) blocklist = [for tup <- [(1, 0), (1, 1), (0, 1), (0, 2)]: vec2i(tup)].eval; // Regular Z block
    for int i <- 0..blocklist.length
      blocklist[i].x += size[0] / 2; // Move the block from the left side to the center of the screen.
    // Aaand .. try to update the block we created above.
    // If this fails, it's game over.
    return current.tryUpdate(tb, blocklist);
  }
  void tryRotate() {
    if !current return; // no active block
    auto newlist = current.poslist.dup;
    rotate(newlist);
    current.tryUpdate(tb, newlist);
  }
  // Sideways movement
  void tryShift(int xshift) {
    if !current return;
    auto newlist = current.poslist.dup;
    for int i <- 0..newlist.length
      newlist[i].x += xshift;
    current.tryUpdate(tb, newlist);
  }
  // Downwards movement.
  void tryDrop() {
    if !current return;
    auto newlist = current.poslist.dup;
    for int i <- 0..newlist.length
      newlist[i].y ++;
    current.tryUpdate(tb, newlist);
  }
  // Should be clear.
  void handleInput() {
         if (keyPushed[SDLK_UP]) tryRotate;
    else if (keyPushed[SDLK_LEFT]) tryShift -1;
    else if (keyPushed[SDLK_RIGHT]) tryShift 1;
    else if (keyPressed[SDLK_DOWN]) tryDrop;
    else return;
    draw(tb);
  }
  // Spawn an initial block.
  tryRemakeCurrentBlock;
  int last = 0; // timekeeping. Blocks are dropped once per second.
  int phase; // Simple two-phase state machine.
  void dropPhase() { // phase 0
    if (!tryMoveDown(current, tb)) { // if this fails, our block has hit the bottom.
      current = null;
      phase = 1;
    }
  }
  void scorePhase() { // 1
    tb.removeFullLines();
    if (!tryRemakeCurrentBlock())
      raise-error new Error "you lose lol"; // lol
    phase = 0; // and go back to dropPhase.
  }
  // The main action of the game.
  void updateGame() {
    [&dropPhase, &scorePhase][phase]();
    draw(tb);
  }
  /*
    Main loop.
    Once every second, update the game state machine.
    Also handle input.
  */
  while true {
    int t = time(null);
    if (t != last) { last = t; updateGame; }
    flip; // SDL helper function to update the screen and poll events.
    handleInput;
  }
}
