#
# FL4's drop-in replacement for seL4's FindseL4.cmake (DESIGN.md §12).
# A seL4 CMake project (sel4test) finds this directory as its "kernel". It
# reuses upstream seL4's configuration machinery from vendor/seL4 through
# the symlinks next to this file, builds libsel4 from FL4's libsel4/, and
# builds kernel.elf with cargo.
#
# SPDX-License-Identifier: GPL-2.0-only
#

cmake_minimum_required(VERSION 3.16.0)

set(KERNEL_PATH "${CMAKE_CURRENT_LIST_DIR}" CACHE STRING "")
set(KERNEL_HELPERS_PATH "${CMAKE_CURRENT_LIST_DIR}/tools/helpers.cmake" CACHE STRING "")
set(KERNEL_CONFIG_PATH "${CMAKE_CURRENT_LIST_DIR}/configs/seL4Config.cmake" CACHE STRING "")
get_filename_component(fl4_cmake_dir "${CMAKE_CURRENT_LIST_DIR}" REALPATH)
get_filename_component(FL4_ROOT "${fl4_cmake_dir}" DIRECTORY)
set(FL4_ROOT "${FL4_ROOT}" CACHE INTERNAL "")
mark_as_advanced(KERNEL_PATH KERNEL_HELPERS_PATH KERNEL_CONFIG_PATH)

macro(sel4_import_kernel)
  add_subdirectory(${KERNEL_PATH} ${CMAKE_BINARY_DIR}/kernel)
endmacro()

macro(sel4_import_libsel4)
  add_subdirectory("${KERNEL_PATH}/libsel4" ${CMAKE_BINARY_DIR}/libsel4)
endmacro()

macro(sel4_configure_platform_settings)
  include(${KERNEL_CONFIG_PATH})
endmacro()

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(seL4 DEFAULT_MSG KERNEL_PATH KERNEL_HELPERS_PATH
                                  KERNEL_CONFIG_PATH)
