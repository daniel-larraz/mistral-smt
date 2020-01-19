# (c) Isil Dillig (isil@cs.stanford.edu), Thomas Dillig (tdillig@cs.stanford.edu)
 
file(GLOB MY_SRC "src/*.cpp")
find_package(PkgConfig)

#The solver ui needs GTKMM to build
#Ideally, we would rewrite this UI in QT at some point...

pkg_check_modules(GTKMM gtkmm-2.4)
 INCLUDE_DIRECTORIES( ${GTKMM_INCLUDE_DIRS} "/usr/include/libglademm-2.4/")
link_directories(${GTKMM_LIBRARY_DIRS}  )
add_executable(mistral_ui ${MY_SRC})
TARGET_LINK_LIBRARIES(mistral_ui ${GTKMM_LIBRARIES})
TARGET_LINK_LIBRARIES(mistral_ui mistral glademm-2.4 gthread-2.0 gmp)
#install(TARGETS mistral_ui  ${INSTALL_TARGETS_DEFAULT_ARGS})
