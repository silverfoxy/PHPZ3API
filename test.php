<?php

$z3_definitions = file_get_contents('defs.c');
$ffi = FFI::cdef($z3_definitions, "/z3-4.8.6-x64-ubuntu-16.04/bin/libz3.so");

$major = FFI::new('unsigned');
$minor = FFI::new('unsigned');
$build = FFI::new('unsigned');
$revision = FFI::new('unsigned');
$ffi->Z3_get_version(FFI::addr($major), FFI::addr($minor), FFI::addr($build), FFI::addr($revision));
echo sprintf('Z3 %d.%d.%d.%d' . PHP_EOL, $major->cdata, $minor->cdata, $build->cdata, $revision->cdata);

?>