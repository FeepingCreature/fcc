module fraclist;

import tools.base;

// TODO unhack this hack
int __dollar = -1;

struct FracList(T) {
  T[][] back;
  void opCatAssign(T[] t) { back ~= t; }
  int length() {
    int res;
    foreach (field; back) res += field.length;
    return res;
  }
  FracList slice(int from, int len) {
    if (len == -1) len = length - from;
    FracList res;
    auto temp = back;
    while (temp[0].length < from) {
      from -= temp.take().length;
    }
    if (from < temp[0].length) {
      if (from+len <= temp[0].length) {
        res.back ~= temp[0][from .. from+len];
        return res;
      }
      auto t = temp.take();
      res.back ~= t[from .. $];
      len -= t.length - from;
    }
    if (len) {
      while (len >= temp[0].length) {
        auto t = temp.take();
        res.back ~= t;
        len -= t.length;
      }
      res.back ~= temp[0][0 .. len];
    }
    return res;
  }
  FracList opSlice(int from, int to = -1) {
    if (to == -1) return slice(from, -1);
    else return slice(from, to - from);
  }
  // fragment id, local id
  void _find(T[] marker, out int fid, out int lid) {
    foreach (i, frac; back) {
      // TODO should tokens be able to span comments?
      auto pos = .find(frac, marker);
      if (pos != -1) {
        fid = i;
        lid = pos;
        return;
      }
    }
    fid = lid = -1;
  }
  int find(T[] marker) {
    int fid, lid;
    _find(marker, fid, lid);
    if (fid == -1) return -1;
    int sum;
    foreach (f; back[0..fid])
      sum += f.length;
    return sum + lid;
  }
  FracList slice(T[] marker) {
    int fid, lid;
    _find(marker, fid, lid);
    auto nfl = *this;
    if (fid == -1) back = null;
    else {
      auto nb = back[fid .. $];
      auto eid = lid + marker.length;
      while (nb.length && nb[0].length <= eid) {
        eid -= nb.take().length;
      }
      
      nfl.back = back[0 .. fid] ~ back[fid][0 .. lid];
      if (eid) back = nb[0][eid .. $] ~ nb[1 .. $];
      else back = nb;
    }
    return nfl;
  }
  FracList[] split(T[] marker) {
    FracList[] res;
    auto temp = *this;
    while (temp.back.length)
      res ~= temp.slice(marker);
    return res;
  }
  string toString() {
    string res;
    foreach (elem; back) res ~= elem;
    return res;
  }
  bool startsWith(T[] marker, out FracList res) {
    int blen = marker.length; // backup
    foreach (frag; back) {
      int cmplen = min(marker.length, frag.length);
      if (frag[0 .. cmplen] != marker[0 .. cmplen])
        return false;
      marker = marker[cmplen .. $];
      if (!marker.length) {
        res = opSlice(blen);
        return true;
      }
    }
    return false; // marker too long
  }
  T[] opCast() {
    T[] res;
    foreach (frac; back) res ~= frac;
    return res;
  }
}

alias FracList!(char) FracString;
