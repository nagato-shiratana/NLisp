cmake_minimum_required(VERSION 3.20)
project(nlisp VERSION 0.1.0 LANGUAGES C)

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

add_library(nlisp_core STATIC src/nlisp.c)
target_include_directories(nlisp_core PUBLIC include)
target_compile_definitions(nlisp_core PRIVATE _CRT_SECURE_NO_WARNINGS)

if(MSVC)
  target_compile_options(nlisp_core PRIVATE /W4 /WX /permissive- /fp:strict)
else()
  target_compile_options(nlisp_core PRIVATE -Wall -Wextra -Wpedantic -Werror -frounding-math)
endif()

add_executable(nlisp src/main.c)
target_link_libraries(nlisp PRIVATE nlisp_core)
find_path(GMP_INCLUDE_DIR gmp.h REQUIRED)
# MinGW distributions normally prefer libgmp.dll.a, which leaves the CLI
# dependent on a DLL in the compiler's bin directory. Ship a standalone CLI.
option(NLISP_STATIC_GMP "Link the static GMP library" ${MINGW})
if(NLISP_STATIC_GMP)
  set(_nlisp_library_suffixes ${CMAKE_FIND_LIBRARY_SUFFIXES})
  if(MSVC)
    set(CMAKE_FIND_LIBRARY_SUFFIXES .lib)
  else()
    set(CMAKE_FIND_LIBRARY_SUFFIXES .a)
  endif()
  find_library(GMP_STATIC_LIBRARY NAMES gmp REQUIRED)
  set(CMAKE_FIND_LIBRARY_SUFFIXES ${_nlisp_library_suffixes})
  set(GMP_LIBRARY ${GMP_STATIC_LIBRARY})
else()
  find_library(GMP_LIBRARY NAMES gmp REQUIRED)
endif()
target_include_directories(nlisp_core PRIVATE ${GMP_INCLUDE_DIR})
target_link_libraries(nlisp_core PUBLIC ${GMP_LIBRARY})
if(MINGW AND NLISP_STATIC_GMP)
  target_link_options(nlisp PRIVATE -static-libgcc)
endif()
if(NOT MSVC)
  target_link_libraries(nlisp_core PUBLIC m)
endif()

include(CTest)
if(BUILD_TESTING)
  find_package(Python3 COMPONENTS Interpreter)
  if(Python3_Interpreter_FOUND)
    add_test(NAME builtins_run COMMAND ${Python3_EXECUTABLE}
      ${CMAKE_CURRENT_SOURCE_DIR}/tests/builtins.py $<TARGET_FILE:nlisp>)
    add_test(NAME syntax_run COMMAND ${Python3_EXECUTABLE}
      ${CMAKE_CURRENT_SOURCE_DIR}/tests/syntax.py $<TARGET_FILE:nlisp>)
    add_test(NAME global_initialization COMMAND ${Python3_EXECUTABLE}
      ${CMAKE_CURRENT_SOURCE_DIR}/tests/global_initialization.py $<TARGET_FILE:nlisp>)
    add_test(NAME independent_certificate COMMAND ${Python3_EXECUTABLE}
      ${CMAKE_CURRENT_SOURCE_DIR}/tests/independent_certificate.py)
    find_program(NLISP_LAKE lake HINTS ${CMAKE_CURRENT_SOURCE_DIR}/.tools/lean-4.8.0/bin
      ${CMAKE_CURRENT_SOURCE_DIR}/.tools/elan-home/bin)
    if(NLISP_LAKE)
      add_test(NAME lean_build COMMAND ${NLISP_LAKE} build)
      set_tests_properties(lean_build PROPERTIES
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} FIXTURES_SETUP lean_library)
      add_test(NAME lean_bridge COMMAND ${Python3_EXECUTABLE}
        ${CMAKE_CURRENT_SOURCE_DIR}/tests/lean_bridge.py $<TARGET_FILE:nlisp> ${NLISP_LAKE})
      add_test(NAME macro_termination COMMAND ${Python3_EXECUTABLE}
        ${CMAKE_CURRENT_SOURCE_DIR}/tests/macro_termination.py $<TARGET_FILE:nlisp> ${NLISP_LAKE})
      add_test(NAME source_reader COMMAND ${Python3_EXECUTABLE}
        ${CMAKE_CURRENT_SOURCE_DIR}/tests/source_reader.py $<TARGET_FILE:nlisp> ${NLISP_LAKE})
      add_test(NAME poly_bridge COMMAND ${Python3_EXECUTABLE}
        ${CMAKE_CURRENT_SOURCE_DIR}/tests/poly_bridge.py $<TARGET_FILE:nlisp> ${NLISP_LAKE})
      set_tests_properties(lean_bridge macro_termination source_reader poly_bridge PROPERTIES
        FIXTURES_REQUIRED lean_library)
      set_tests_properties(builtins_run syntax_run global_initialization independent_certificate
        lean_bridge macro_termination source_reader poly_bridge PROPERTIES
        ENVIRONMENT "PYTHONUTF8=1")
      foreach(model SurfaceIR Erasure ErasureMagnitude EvaluatorCorrectness ErasureExecution SurfaceChecker ExpansionLowering NameLowering TypeArguments PolymorphicSafety GlobalIR CheckerCompleteness)
        add_test(NAME lean_${model} COMMAND ${NLISP_LAKE} env lean tests/${model}.lean)
        set_tests_properties(lean_${model} PROPERTIES
          WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} FIXTURES_REQUIRED lean_library)
      endforeach()
    endif()
  endif()
  add_test(NAME factorial_check COMMAND nlisp check ${CMAKE_CURRENT_SOURCE_DIR}/examples/factorial.nlisp)
  add_test(NAME builtins_example COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/examples/builtins.nlisp)
  set_tests_properties(builtins_example PROPERTIES PASS_REGULAR_EXPRESSION "42")
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

  add_test(NAME integer_unbounded COMMAND nlisp run ${CMAKE_CURRENT_SOURCE_DIR}/tests/overflow.nlisp)
  set_tests_properties(integer_unbounded PROPERTIES PASS_REGULAR_EXPRESSION "9223372036854775808")
endif()
