module cpuid;

void main() {
  {
    auto temp = cpuid 0;
    auto ident = char[12]:(temp[1], temp[3], temp[2]);
    writeln "Vendor ID: $ident";
  }
  {
    auto temp = cpuid 1;
    writeln "Processor Info: signature $(temp[0]); feature flags $(temp[3]), $(temp[2]); additional info $(temp[1])";
  }
  {
    auto temp = cpuid 0x8000_0000;
    if (temp[0] >= 0x8000_0004) {
      auto brand = char[16]:(cpuid 0x8000_0002) ~ char[16]:(cpuid 0x8000_0003) ~ char[16]:(cpuid 0x8000_0004);
      writeln "Processor brand: $brand";
    }
  }
}
