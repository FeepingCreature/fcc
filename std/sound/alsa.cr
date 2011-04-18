module std.sound.alsa;

import std.c.alsa.pcm, std.sound.base, std.string;

alias Sample = Sample;

extern(C) {
  int snd_pcm_open(snd_pcm_t** pcm, char* name, int stream, int mode);
  int snd_pcm_set_params(snd_pcm_t*, int, int, int channels, int rate, int soft_resample, int latency);
  int snd_pcm_writei(snd_pcm_t*, void* buffer, int size);
  char* snd_strerror(int);
}

template check(alias A) <<EOT
  void check(ParamTypes type-of &A a) {
    auto res = A a;
    if res == 0 return;
    else raise-error new Error "While calling $(string-of A): $res: $(CToString snd_strerror res)";
  }
EOT

context Stream {
  alias Playback = 0;
}

context SndFormat {
  alias Unknown = -1;
  alias S8 = 0; alias U8 = 1;
  alias S16_LE = 2; alias S16_BE = 3;
  alias U16_LE = 4; alias U16_BE = 5;
}

context Access {
  alias MMap_Interleaved = 0; alias MMap_NonInterleaved = 1; alias MMap_Complex = 2;
  alias RW_Interleaved = 3; alias RW_NonInterleaved = 4;
}

class AlsaSound : Sound {
  snd_pcm_t* hdl;
  string name;
  void init(string n) { name = n; }
  void open() {
    auto foo = Stream.Playback;
    check!snd_pcm_open(&hdl, toStringz name, Stream.Playback,  0);
    check!snd_pcm_set_params(hdl, SndFormat.S16_LE, Access.RW_Interleaved, 1, 48000, 1, 400000);
    check!snd_pcm_nonblock(hdl, false);
  }
  void close() {
    check!snd_pcm_close(hdl);
    hdl = null;
  }
  void writeCopydump(int len) {
    bool closeAfter;
    if !hdl { open(); closeAfter = true; }
    onExit if (closeAfter) close();
    auto cd = copydump[0 .. len];
    while true {
      // writeln "< $(cd.length)";
      // writeln "$cd";
      auto frames = snd_pcm_writei(hdl, cd.ptr, cd.length);
      if (frames < 0) {
        writeln "Attempt to recover: $frames";
        frames = snd_pcm_recover(hdl, frames, 0);
      }
      if (frames < 0) {
        writeln "Write failure! ";
        return;
      }
      if (frames < cd.length) {
        writeln "Short write: expected $(cd.length), got $frames";
        cd = cd[frames .. $];
      } else return;
    }
  }
}
