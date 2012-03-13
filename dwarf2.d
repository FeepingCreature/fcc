module dwarf2;

import asmfile, quickformat;
import tools.ctfe: ctTableUnroll;
import tools.base: Stuple, stuple;
import tools.log;

// _ATE to prevent collision with AT
const string DwarfCodeTable = `
  value | TAG            | AT          | FORM   | OP     | _ATE
  ------+----------------+-------------+--------+--------+------
  0x00  |                |             |        |        | void
  0x01  | array_type     |             | addr   |        | address
  0x02  | class_type     | location    |        |        | boolean
  0x03  |                | name        |        |        | complex_float
  0x04  |                |             |        |        | float
  0x05  |                |             |        |        | signed
  0x06  |                |             | data4  |        | signed_char
  0x07  |                |             |        |        | unsigned
  0x08  |                |             | string |        | unsigned_char
  0x09  |                |             |        |        | imaginary_float
  0x0a  |                |             | block1 |        | packed_decimal
  0x0b  | lexical_block  | byte_size   | data1  |        | numeric_string
  0x0c  |                |             | flag   |        | edited
  0x0d  | member         |             |        |        | signed_fixed
  0x0e  |                |             | strp   |        | unsigned_fixed
  0x0f  | pointer_type   |             |        |        | decimal_float
  0x10  | reference_type | stmt_list   |        |        |
  0x11  | compile_unit   | low_pc      |        |        |
  0x12  | string_type    | high_pc     |        |        |
  0x13  | structure_type | language    | ref4   |        |
  0x1b  |                | comp_dir    |        |        |
  0x24  | base_type      |             |        |        |
  0x25  |                | producer    |        |        |
  0x27  |                | prototyped  |        |        |
  0x2e  | subprogram     |             |        |        |
  0x34  | variable       |             |        |        |
  0x38  |       | data_member_location |        |        |
  0x3a  |                | decl_file   |        |        |
  0x3b  |                | decl_line   |        |        |
  0x3e  |                | encoding    |        |        |
  0x3f  |                | external    |        |        |
  0x40  |                | frame_base  |        |        |
  0x49  |                | type        |        |        |
  0x50  |                |             |        | reg0   |
  0x51  |                |             |        | reg1   |
  0x52  |                |             |        | reg2   |
  0x53  |                |             |        | reg3   |
  0x54  |                |             |        | reg4   |
  0x55  |                |             |        | reg5   |
  0x56  |                |             |        | reg6   |
  0x57  |                |             |        | reg7   |
  0x91  |                |             |        | fbreg  |
`;

mixin(`
string makeDWEnum() {
  string res = "enum DW {";
  `~DwarfCodeTable.ctTableUnroll(`
    if ("$TAG".length)
      res ~= "TAG_$TAG = $value,";
    if ("$AT".length)
      res ~= "AT_$AT = $value,";
    if ("$FORM".length)
      res ~= "FORM_$FORM = $value,";
    if ("$OP".length)
      res ~= "OP_$OP = $value,";
    if ("$_ATE".length)
      res ~= "ATE_$_ATE = $value,";
  `) ~ `
  res ~= "children_no = false, children_yes = true }";
  return res;
}
`);
mixin(makeDWEnum());

string[] formatAbbrevSection(int key, DW[] data) {
  string[] res;
  void addLine(string s) { res ~= s; }
  void addWide(DW value, string comment) {
    addLine(qformat(".uleb128 ", hex(value), "\t/* ", comment, " */"));
  }
  void add(DW dw, string mode) {
    string tagname, atname, formname;
    mixin(`
    switch (dw) {
      `~DwarfCodeTable.ctTableUnroll(`
      case cast(DW) $value:
        tagname = "DW_TAG_$TAG";
        atname = "DW_AT_$AT";
        formname = "DW_FORM_$FORM";
        break;
      `)~`
      default: break;
    }`);
    string comment;
    switch (mode) {
      case "TAG":
        if (!tagname || tagname == "DW_TAG_") fail;
        comment = "TAG: "~tagname;
        break;
      case "AT":
        if (!atname || atname == "DW_AT_") fail;
        comment = atname;
        break;
      case "FORM":
        if (!formname || formname == "DW_FORM_") fail;
        comment = formname;
        break;
    }
    addWide(dw, comment);
  }
  DW[] rest = data;
  DW take() {
    auto res = rest[0];
    if (!rest.length) fail;
    rest = rest[1..$];
    return res;
  }
  
  addWide(cast(DW) key, "abbrev code");
  add(take(), "TAG");
  {
    auto ch = take();
    if (ch == DW.children_no)
      addLine(".byte 0\t /* DW_children_no */");
    else if (ch == DW.children_yes)
      addLine(".byte 1\t /* DW_children_yes */");
    else fail;
  }
  while (rest.length) {
    auto at = take(), form = take();
    add(at, "AT");
    add(form, "FORM");
  }
  addLine(".byte 0");
  addLine(".byte 0");
  return res;
}

class Dwarf2AbbrevCache {
  Stuple!(DW[], int)[string] abbrevs;
  void allocAbbrev(string name, DW[] data) {
    int key = cast(int) abbrevs.length + 1;
    abbrevs[name] = stuple(data, key);
  }
  Stuple!(bool, int) getKeyFor(string name) {
    auto tup = name in abbrevs;
    if (!tup) fail;
    return stuple(tup._0[1] == DW.children_yes, tup._1);
  }
  string[] genSection() {
    string[] res;
    res ~= ".section\t.debug_abbrev";
    res ~= ".Ldebug_abbrev0:";
    foreach (key, value; abbrevs) {
      res ~= formatAbbrevSection(value._1, value._0);
    }
    res ~= ".byte 0";
    return res[];
  }
}

class Dwarf2Strings {
  string[] strings;
  string addString(string s) {
    auto key = qformat(".long\t.LSTRING", strings.length);
    strings ~= s;
    return key;
  }
  string[] genSection() {
    string[] res;
    res ~= ".section\t.debug_str";
    foreach (i, v; strings) {
      res ~= qformat(".LSTRING", i, ":");
      res ~= qformat("\t.string \"", v, "\"");
    }
    return res;
  }
}

string hex(int i) {
  string res;
  while (i) {
    res = "0123456789abcdef"[i&15] ~ res;
    i /= 16;
  }
  return "0x"~res;
}

int keycounter;
class Dwarf2Section {
  Dwarf2Section sup;
  Dwarf2Section[] sub;
  int key;
  int abbrev;
  bool has_children;
  string[] data;
  string comment;
  this(Stuple!(bool, int) info) {
    synchronized key = keycounter ++;
    has_children = info._0;
    abbrev = info._1;
  }
  string getLabel() {
    return qformat(".Ldie", key);
  }
  string getRelative() {
    return qformat(".long\t", getLabel(), " - d", "\t/* relative: ", abbrev, " */");
  }
  string[] genSection() {
    string[] res;
    res ~= getLabel()~":"~(comment?qformat("\t/* ", comment, " */"):"");
    res ~= qformat(".uleb128 ", hex(abbrev), "\t/* abbrev code */");
    res ~= data;
    foreach (sect; sub)
      res ~= sect.genSection();
    if (has_children)
      res ~= ".byte\t0\t/* end of "~getLabel()~" */";
    return res;
  }
}

class Dwarf2Controller {
  Dwarf2AbbrevCache cache;
  Dwarf2Section root, current;
  Dwarf2Strings strings;
  Dwarf2Section[string] rootsections;
  this() {
    New(strings);
    New(cache);
    cache.allocAbbrev("compile unit",
      [DW.TAG_compile_unit,
       DW.children_yes,
       DW.AT_producer,  DW.FORM_strp,
       DW.AT_language,  DW.FORM_data1,
       DW.AT_name,      DW.FORM_strp,
       DW.AT_low_pc,    DW.FORM_addr,
       DW.AT_high_pc,   DW.FORM_addr,
       DW.AT_stmt_list, DW.FORM_data4
      ]);
    New(root, cache.getKeyFor("compile unit"));
    root.data ~= strings.addString("Neat FCC 1");
    root.data ~= ".byte\t0x1\t/* language whatevs */";
    root.data ~= strings.addString("test.nt");
    root.data ~= ".long .Ltext";
    root.data ~= ".long .Letext";
    // root.data ~= ".4byte\t.Ldebug_line0";
    root.data ~= ".long\t.Ldebug_line0";
    current = root;
    
    cache.allocAbbrev("subprogram",
      [DW.TAG_subprogram,
       DW.children_yes,
       DW.AT_external,  DW.FORM_flag,
       DW.AT_name,      DW.FORM_strp,
       DW.AT_decl_file, DW.FORM_data4,
       DW.AT_decl_line, DW.FORM_data4,
       DW.AT_prototyped,DW.FORM_flag,
       DW.AT_low_pc,    DW.FORM_addr,
       DW.AT_high_pc,   DW.FORM_addr,
       DW.AT_frame_base,DW.FORM_block1
      ]);
    cache.allocAbbrev("lexical block",
      [DW.TAG_lexical_block,
       DW.children_yes,
       DW.AT_low_pc,  DW.FORM_addr,
       DW.AT_high_pc, DW.FORM_addr
      ]);
    cache.allocAbbrev("variable",
      [DW.TAG_variable,
       DW.children_no,
       DW.AT_name,     DW.FORM_strp,
       DW.AT_type,     DW.FORM_ref4,
       DW.AT_location, DW.FORM_block1
      ]);
    cache.allocAbbrev("base type",
      [DW.TAG_base_type,
       DW.children_no,
       DW.AT_byte_size, DW.FORM_data4,
       DW.AT_encoding,  DW.FORM_data1,
       DW.AT_name,      DW.FORM_strp
      ]);
    cache.allocAbbrev("structure type",
      [DW.TAG_structure_type,
       DW.children_yes,
       DW.AT_byte_size, DW.FORM_data4
      ]);
    cache.allocAbbrev("pointer type",
      [DW.TAG_pointer_type,
       DW.children_no,
       DW.AT_type,      DW.FORM_ref4,
       DW.AT_byte_size, DW.FORM_data4
      ]);
    cache.allocAbbrev("array type",
      [DW.TAG_array_type,
       DW.children_no,
       DW.AT_type,      DW.FORM_ref4,
       DW.AT_byte_size, DW.FORM_data4
      ]);
    cache.allocAbbrev("structure member",
      [DW.TAG_member,
       DW.children_no,
       DW.AT_name, DW.FORM_strp,
       DW.AT_type, DW.FORM_ref4,
       DW.AT_data_member_location, DW.FORM_block1
      ]);
  }
  void open(Dwarf2Section sect) {
    current.sub ~= sect;
    sect.sup = current;
    current = sect;
  }
  void close() {
    current = current.sup;
  }
  void closeUntil(Dwarf2Section dest) {
    while (current !is dest) close;
  }
  void add(Dwarf2Section sect) {
    open(sect);
    close;
  }
  string addToRoot(string key, lazy Dwarf2Section sect) {
    if (auto p = key in rootsections) {
      return p.getRelative();
    }
    auto s = sect();
    rootsections[key] = s;
    s.sup = root;
    return s.getRelative();
  }
  string[] genData() {
    string[] res;
    res ~= ".section\t.debug_info";
    res ~= ".Ldebug_info0:";
    res ~= "d:";
    // res ~= ".4byte\t.Lcu_end - 1f\t/* length */";
    res ~= ".long\t.Lcu_end - 1f\t/* length */";
    res ~= "1:";
    res ~= ".value\t0x2\t/* dwarf version */";
    res ~= ".long\t.Ldebug_abbrev0";
    res ~= ".byte\t0x4\t/* pointer size */";
    foreach (key, value; rootsections) {
      value.comment = ":"~key;
      root.sub ~= value;
    }
    res ~= root.genSection();
    res ~= ".Lcu_end:";
    res ~= cache.genSection();
    res ~= strings.genSection();
    return res;
  }
}

interface Dwarf2Encodable {
  bool canEncode();
  Dwarf2Section encode(Dwarf2Controller);
}
