cmake_minimum_required(VERSION 3.20)
project(nlisp VERSION 0.1.0 LANGUAGES C)

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

add_library(nlisp_core STATIC src/nlisp.c)
target_include_directories(nlisp_core PUBLIC include)
target_compile_definitions(nlisp_core PRIVATE _CRT_SECURE_NO_WARNINGS)

if(MSVC)
  target_compile_options(nlisp_core PRIVATE /W4 /WX /permissive-)
else()
  target_compile_options(nlisp_core PRIVATE -Wall -Wextra -Wpedantic -Werror)
endif()

add_executable(nlisp src/main.c)
target_link_libraries(nlisp PRIVATE nlisp_core)

include(CTest)
if(BUILD_TESTING)
  add_test(NAME factorial_check COMMAND nlisp check ${CMAKE_CURRENT_SOURCE_DIR}/examples/factorial.nlisp)
  add_test(NAME factorial_run COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/examples/factorial.nlisp)
  set_tests_properties(factorial_run PROPERTIES PASS_REGULAR_EXPRESSION "120")

  add_test(NAME list_run COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/examples/list_length.nlisp)
  set_tests_properties(list_run PROPERTIES PASS_REGULAR_EXPRESSION "3")

  add_test(NAME option_run COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/examples/option.nlisp)
  set_tests_properties(option_run PROPERTIES PASS_REGULAR_EXPRESSION "42")

  add_test(NAME closure_run COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/examples/closure.nlisp)
  set_tests_properties(closure_run PROPERTIES PASS_REGULAR_EXPRESSION "42")

  add_test(NAME mutual_recursion_run COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/examples/mutual_recursion.nlisp)
  set_tests_properties(mutual_recursion_run PROPERTIES PASS_REGULAR_EXPRESSION "1")

  add_test(NAME reject_type_error COMMAND nlisp check ${CMAKE_CURRENT_SOURCE_DIR}/tests/type_error.nlisp)
  set_tests_properties(reject_type_error PROPERTIES WILL_FAIL TRUE)

  add_test(NAME reject_overflow COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/tests/overflow.nlisp)
  set_tests_properties(reject_overflow PROPERTIES WILL_FAIL TRUE)
endif()
