module std.sort;

template qsort(alias Smaller) << EOT1
  template qsort(T) << EOT2
    void qsort(T array) {
      void qsort_recurse(int from, to) {
        if (to == from || to == from + 1) return;
        if (to == from + 2) {
          if (!mixin(Smaller.replace("%a", "array[from]").replace("%b", "array[to - 1]")))
            array[(from, to - 1)] = array[(to - 1, from)];
          return;
        }
        int pivot = (to + from) / 2;
        auto pival = array[pivot];
        array[(pivot, to - 1)] = array[(to - 1, pivot)];
        pivot = to - 1;
        auto store = from;
        // thanks wp
        for int i <- from..to {
          if (mixin(Smaller.replace("%a", "array[i]").replace("%b", "pival"))) {
            array[(i, store)] = array[(store, i)];
            store ++;
          }
        }
        array[(store, pivot)] = array[(pivot, store)];
        qsort_recurse(from, store);
        qsort_recurse(store, to);
      }
      qsort_recurse(0, array.length);
    }
  EOT2
EOT1
