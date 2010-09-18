/*
 *  The file input.h  -- Juhana Kouhia, jk87377@cs.tut.fi, Oct. 25, 1991
 *
 *  Load_patch(filename, patches, verticies);
 *    char *filename; int *patches, *verticies;  
 *    A sample program to read Bezier patches in.
 *    Returns count of patches and verticies.
 *  User defined subroutines:
 *    B_patch(ii, a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p);
 *      int ii, a, b, ..., p;
 *      Defines one Bezier patch with index number ii,
 *      indexes to points are in a, b, c, ..., p.
 *    B_point(ii, x, y, z);
 *      int ii; double x, y, z;
 *      Defines one point with index number ii.
 */

extern void Load_patch();
