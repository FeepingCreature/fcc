// ported from qd
module sdl_ttf;

import sdl, std.string, c.SDL.SDL_ttf;

int deflt_size = 14;

struct fontsettings {
  bool bold, italic, underline;
  vec3f color;
  int size;
}

fontsettings deflt;

void init() {
  TTF_Init;
  deflt.color = vec3f(1);
}

SDL_Color mkSDLColor(vec3f v) {
  SDL_Color res;
  // todo: wtf
  res.r = char:short:int:(v.x * 255);
  res.g = char:short:int:(v.y * 255);
  res.b = char:short:int:(v.z * 255);
  return res;
}

extern(C) {
  SDL_Surface* TTF_RenderUTF8_Solid
    (TTF_Font* font, char* text, SDL_Color fg);
  SDL_Surface* TTF_RenderUTF8_Shaded
    (TTF_Font* font, char* text, SDL_Color fg, SDL_Color bg);
  SDL_Surface* TTF_RenderUTF8_Blended
    (TTF_Font* font, char* text, SDL_Color fg);
  TTF_Font* TTF_OpenFontRW
    (SDL_RWops* src, int freesrc, int ptsize);
  char* SDL_GetError();
}

class TTF_FontClass {
  TTF_Font* font;
  int height() { return TTF_FontHeight font; }
  int ascent() { return TTF_FontAscent font; }
  int descent() { return TTF_FontDescent font; }
  int lineskip() { return TTF_FontLineSkip font; }
  int getWidth(string text) {
    TTF_SizeUTF8 (font, text.toStringz(), &int w, &int h);
    return w;
  }
  int curStyle;
  Area render(string text, fontsettings s = deflt, int rendermode = 2, SDL_Color* bg = SDL_Color*: null) {
    
    int style;
    using s
      style = [0,1][bold] + [0,2][italic] + [0,4][underline];
    
    if (curStyle != style) TTF_SetFontStyle (font, style);
    
    curStyle = style;
    
    /// Text mode: 0=Latin1, 1=UTF8, 2=Unicode
    if (rendermode == 0) // solid
      return new Area new Surface TTF_RenderUTF8_Solid (font, text.toStringz(), mkSDLColor(s.color));
    if (rendermode == 1) {// shaded
      if !bg raise-error new Error "Shaded selected but no background color given! ";
      return new Area new Surface TTF_RenderUTF8_Shaded (font, text.toStringz(), mkSDLColor(s.color), *bg);
    }
    if (rendermode == 2) {
      return new Area new Surface TTF_RenderUTF8_Blended (font, text.toStringz(), mkSDLColor(s.color));
    }
    raise-error new Error "Invalid case";
  }
  void[] file_buffer;
  void init(void[] file, int ptsize) {
    file_buffer = file;
    font = TTF_OpenFontRW (SDL_RWFromMem (file.ptr, file.length), 1, ptsize);
    if !font
      raise-error
        new Error
          "TTF_FontClass.this: Couldn't open font: $(CToString(SDL_GetError())))";
  }
  void fini() { TTF_CloseFont(font); }
}
