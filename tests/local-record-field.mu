; The expected type reaches into a record, so the wrong field is blamed
the {.a : [#x], .b : [#y]} {.a = #x, .b = #z}
