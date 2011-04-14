module csdl;

c_include "SDL/SDL.h";

/*
RenameIdentifier SDL_RWops _cparsed_SDL_RWops;

extern(C) {
  struct SDL_RWops {
    int function(SDL_RWops*, int offs, int whence) seek;
    int function(SDL_RWops*, void* ptr, int size, int maxnum) read;
    int function(SDL_RWops*, void* ptr, int size, int num) write;
    int function(SDL_RWops*) close;
    int type;
    void*[4] filler;
  }
}
*/

RenameIdentifier SDL_Rect CSDL_Rect;

struct SDL_Rect {
  short x, y, w, h;
}

RenameIdentifier SDL_UpperBlit CSDL_UpperBlit;
extern(C) int SDL_UpperBlit(SDL_Surface*, SDL_Rect*, SDL_Surface*, SDL_Rect*);

