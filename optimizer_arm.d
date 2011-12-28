module optimizer_arm;

import optimizer_base;

bool armOptsSetup;
void setupARMOpts() {
  synchronized {
    if (armOptsSetup) return;
    armOptsSetup = true;
  }
}
