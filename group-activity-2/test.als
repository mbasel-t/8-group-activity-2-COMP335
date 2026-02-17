var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not File = f       // guard
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

pred delete_permanent_from_trash [f : File] {
    not File = f       // guard
    f in Trash         // guard
    Trash' = Trash - f // effect on Trash
    File' = File - f   // effect on File
}

pred delete_permanent_outside_trash [f : File] {
    not File = f       // guard
    not (f in Trash)   // guard
    Trash' = Trash     // frame condition on Trash
    File' = File - f   // effect on File
}

pred empty_trash {
  Trash != none        // guard
  not File = Trash     // guard
  Trash' = none        // effect on Trash
  File' = File - Trash // effect on File
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f] or delete_permanent_from_trash[f] or delete_permanent_outside_trash[f]))
}

pred example {} // to ensure we can do higher bound instances
run example for 10 File