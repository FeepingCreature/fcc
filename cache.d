module cache;

import quickformat;
import tools.base: read, write, split, join, slice, fail, mkdir;
import tools.log: logln;

string[] include_path;

static this() {
  include_path ~= "/usr/local/include";
  include_path ~= "/usr/include";
  version(Windows) include_path ~= "/mingw/include";
}

import memconserve_stdfile;
alias memconserve_stdfile.exists exists;
alias memconserve_stdfile.getTimes getTimes;

private bool earlier(long t1, long t2) { return t1 < t2; }

private bool older  (long t1, long t2) { return t1 > t2; }

// is file1 older than file2? if it's newer, must regenerate file2.
bool isUpToDate(string file1, string file2) {
  long created1, accessed1, modified1, created2, accessed2, modified2;
  file1.getTimes(created1, accessed1, modified1);
  file2.getTimes(created2, accessed2, modified2);
  return earlier(modified1, modified2);
}

bool mustReread(string source, string product) {
  if (!product.exists()) return true;
  return !isUpToDate(source, product);
}

extern(C) long atoll(char* c);
long atol(string s) {
  string cstr = qformat(s, "\0");
  return atoll(cstr.ptr);
}

string findfile(string file) {
  if (file.exists()) return file;
  foreach (entry; include_path)
    if (entry.qsub(file).exists()) return entry.qsub(file);
  return null;
}

bool cachefile_read;
string[string] cachedata;

void check_cache() {
  if (!cachefile.exists()) return;
  if (!cachefile_read) {
    foreach (line; (cast(string) read(cachefile)).split("\n")) {
      auto lkey = line.slice("=");
      cachedata[lkey] = line;
    }
    cachefile_read = true;
  }
}

const cachefile = ".obj/cache.txt";
string read_cache(string key, string filekey) {
  if (filekey) {
    filekey = findfile(filekey);
    if (!filekey || !filekey.exists()) {
      logln("?? '", filekey, "'");
      fail;
    }
  }
  if (!cachefile.exists()) return null;
  check_cache();
  
  if (filekey) {
    auto age = qformat("age ", filekey, " ", key);
    if (!(age in cachedata)) return null;
    long created, accessed, modified;
    filekey.getTimes(created, accessed, modified);
    long mod2 = cachedata[age].atol();
    if (older(modified, mod2)) // if the cache is older than our file
      return null;
  }
  
  auto fullkey = qformat("key ", filekey, " ", key);
  if (!(fullkey in cachedata)) {
    if (filekey) {
      logln("cache for ", key, ", ", filekey, " tracks age but not data");
      fail;
    } else return null;
  }
  
  return cachedata[fullkey];
}

double last_saved = 0;

import tools.time: sec;

void write_cache(string key, string filekey, string data) {
  if (filekey) {
    filekey = findfile(filekey);
    if (!filekey || !filekey.exists()) {
      logln("!! ", filekey);
      fail;
    }
  }
  
  check_cache();
  
  auto fullkey = qformat("key ", filekey, " ", key);
  if (filekey) {
    long created, accessed, modified;
    filekey.getTimes(created, accessed, modified);
    auto agekey = qformat("age ", filekey, " ", key);
    cachedata[agekey] = qformat(modified);
  }
  cachedata[fullkey] = data;
}

void save_cache() {
  string[] lines;
  foreach (key, value; cachedata) lines ~= qformat(key, "=", value);
  
  if (!".obj".exists()) mkdir(".obj");
  
  scope data = lines.join("\n");
  write(cachefile, data);
}
