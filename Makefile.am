bin_PROGRAMS=gtktweeter
gtktweeter_SOURCES=gtktweeter.c parson.c parson.h
AM_CPPFLAGS=-DDATA_DIR=\"$(pkgdatadir)\" -DLOCALE_DIR=\"$(datadir)/locale\"
gtktweeter_LDADD=${GTK_LIBS}
dist_pkgdata_DATA=data/twitter.png data/loading.gif data/reload.png data/replies.png data/config.png data/post.png data/home.png data/logo.png data/search.png
EXTRA_DIST=gtktweeter.spec
