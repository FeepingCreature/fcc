module memconserve_stdfile;

import quickformat, std.file, std.date, std.string;

// std.file with more delete()

version(Win32) {
  import std.c.windows.windows;
  void getTimes(char[] name, out d_time ftc, out d_time fta, out d_time ftm)
  {
    HANDLE findhndl;
    
    if (useWfuncs)
    {
      WIN32_FIND_DATAW filefindbuf;
      
      auto nameptr = std.utf.toUTF16z(name);
      scope(exit) delete nameptr;
      findhndl = FindFirstFileW(nameptr, &filefindbuf);
      ftc = std.date.FILETIME2d_time(&filefindbuf.ftCreationTime);
      fta = std.date.FILETIME2d_time(&filefindbuf.ftLastAccessTime);
      ftm = std.date.FILETIME2d_time(&filefindbuf.ftLastWriteTime); 
    }
    else
    {   
      WIN32_FIND_DATA filefindbuf;
      
      auto nameptr = toMBSz(name);
      scope(exit) delete nameptr;
      findhndl = FindFirstFileA(nameptr, &filefindbuf);
      ftc = std.date.FILETIME2d_time(&filefindbuf.ftCreationTime);
      fta = std.date.FILETIME2d_time(&filefindbuf.ftLastAccessTime);
      ftm = std.date.FILETIME2d_time(&filefindbuf.ftLastWriteTime); 
    }

    if (findhndl == cast(HANDLE)-1)
    {
      throw new FileException(name, GetLastError());
    }
    FindClose(findhndl);
  }
  int exists(char[] name)
  {
    uint result;
    
    if (useWfuncs) {
      // http://msdn.microsoft.com/library/default.asp?url=/library/en-us/fil
      auto nameptr = std.utf.toUTF16z(name);
      scope(exit) delete nameptr;
      result = GetFileAttributesW(nameptr);
    } else {
      auto nameptr = toMBSz(name);
      scope(exit) delete nameptr;
      result = GetFileAttributesA(nameptr);
    }
    
    return result != 0xFFFFFFFF;
  } 
} else {
  import std.c.unix.unix, std.c.stdlib;
  void getTimes(string name, out d_time ftc, out d_time fta, out d_time ftm)
  {
    auto namez = qformat(name, "\0").ptr;
    
    struct_stat statbuf;
    if (unix.stat(namez, &statbuf))
    {
      throw new FileException(name, getErrno());
    }
    version (GNU)
    {
      ftc = cast(d_time)statbuf.st_ctime * std.date.TicksPerSecond;
      fta = cast(d_time)statbuf.st_atime * std.date.TicksPerSecond;
      ftm = cast(d_time)statbuf.st_mtime * std.date.TicksPerSecond;
    }
    else version (linux)
    {
      ftc = cast(d_time)statbuf.st_ctime * std.date.TicksPerSecond;
      fta = cast(d_time)statbuf.st_atime * std.date.TicksPerSecond;
      ftm = cast(d_time)statbuf.st_mtime * std.date.TicksPerSecond;
    }
    else version (OSX)
    {   // BUG: should add in tv_nsec field
      ftc = cast(d_time)statbuf.st_ctimespec.tv_sec * std.date.TicksPerSecond;
      fta = cast(d_time)statbuf.st_atimespec.tv_sec * std.date.TicksPerSecond;
      ftm = cast(d_time)statbuf.st_mtimespec.tv_sec * std.date.TicksPerSecond;
    }
    else version (FreeBSD)
    {   // BUG: should add in tv_nsec field
      ftc = cast(d_time)statbuf.st_ctimespec.tv_sec * std.date.TicksPerSecond;
      fta = cast(d_time)statbuf.st_atimespec.tv_sec * std.date.TicksPerSecond;
      ftm = cast(d_time)statbuf.st_mtimespec.tv_sec * std.date.TicksPerSecond;
    }
    else version (Solaris)
    {  // BUG: should add in *nsec fields
      ftc = cast(d_time)statbuf.st_ctime * std.date.TicksPerSecond;
      fta = cast(d_time)statbuf.st_atime * std.date.TicksPerSecond;
      ftm = cast(d_time)statbuf.st_mtime * std.date.TicksPerSecond;
    }
    else
    {
      static assert(0);
    }
  }
  int exists(char[] name)
  {
    auto nameptr = qformat(name, "\0").ptr;
    return access(nameptr, 0) == 0;
  }
}
