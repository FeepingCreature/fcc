module std.sound.notesynth;

import std.math, std.random;

class Note {
  float maxVolume, sustain;
  float decayStart, sustainStart, releaseStart;
  float end;
  float freq;
  float calcVolume(float pos) {
    if pos < decayStart
      return pos * maxVolume / decayStart;
    if pos < sustainStart
      return maxVolume - (pos - decayStart) * (maxVolume - sustain) / (sustainStart - decayStart);
    if pos < releaseStart
      return sustain;
    if pos < end
      return sustain - (pos - releaseStart) * sustain / (end - releaseStart);
    return 0;
  }
  float baseCalc(float pos) { writeln "baseCalc in note: need override"; _interrupt 3; }
  float calcValue(float pos) {
    // auto val = sin(pos * freq * 2 * PI);
    auto val = baseCalc pos;
    val = val * 2 - 1;
    return val * calcVolume(pos);
  }
  bool contains(float f) { return eval f >= 0 && f < end; }
}

class SineNote : Note {
  float baseCalc(float pos) {
    return sin(pos * freq * 2 * PI);
  }
}

class RectNote : Note {
  float baseCalc(float pos) {
    auto p2 = pos * freq;
    auto val = (p2 - floorf p2);
    if val > 0.5 val = 1;
    else val = 0;
    return val;
  }
}

class KarplusStrongNote : Note {
  float[] samples;
  float prevInt, prevRes;
  float baseCalc(float pos) {
    int length = int:(48000 / freq);
    if !samples.length {
      samples = new float[length];
      auto rng = getPRNG 23;
      for int i <- 0..length
        samples[i] = randf(rng) * 2 - 1;
      prevInt = 0; prevRes = 0;
    }
    int c = int:(pos * freq * length) % length, d = (c + 1) % length;
    samples[d] = (samples[c] + samples[d]) * 0.5 * 0.999;
    alias C = 0.5;
    auto res = samples[d];
    (float prev, prevInt) = (prevInt, res);
    res = C * res + prev - C * prevRes;
    prevRes = res;
    return res;
  }
}
