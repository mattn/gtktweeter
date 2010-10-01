/* Copyright 2010 by Yasuhiro Matsumoto
 * modification, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#include <gtk/gtk.h>
#include <gdk-pixbuf/gdk-pixbuf.h>
#include <gdk/gdkkeysyms.h>
#include <glib/gconvert.h>
#include <glib/gstdio.h>
#include <libxml/parser.h>
#include <libxml/xpath.h>
#include <libxml/xpathInternals.h>
#include <ctype.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <curl/curl.h>
#include <memory.h>
#include <libintl.h>
#ifdef _WIN32
# include <io.h>
#endif

#ifdef _LIBINTL_H
# include <locale.h>
# define _(x) gettext(x)
#else
# define _(x) x
#endif

#ifdef _WIN32
# define DATA_DIR "data"
# define LOCALE_DIR "share/locale"
# ifndef snprintf
#  define snprintf _snprintf
# endif
# ifndef strncasecmp
#  define strncasecmp(d,s,n) strnicmp(d,s,n)
# endif
# ifndef srandom
#  define srandom(s) srand(s)
# endif
# ifndef random
#  define random() rand()
# endif
#endif

#define APP_TITLE                  "GtkTweeter"
#define APP_NAME                   "gtktweeter"
#define APP_VERSION                "0.1.0"
#define SERVICE_SEARCH_STATUS_URL  "http://search.twitter.com/search.rss"
#define SERVICE_RATE_LIMIT_URL     "http://api.twitter.com/1/account/rate_limit_status.xml"
#define SERVICE_USER_SHOW_URL      "https://api.twitter.com/1/users/show/%s.xml"
#define SERVICE_UPDATE_URL         "https://api.twitter.com/1/statuses/update.xml"
#define SERVICE_RETWEET_URL        "https://api.twitter.com/1/statuses/retweet/%s.xml"
#define SERVICE_FAVORITE_URL       "https://api.twitter.com/1/favorites/create/%s.xml"
#define SERVICE_UNFAVORITE_URL     "https://api.twitter.com/1/favorites/destroy/%s.xml"
#define SERVICE_REPLIES_STATUS_URL "https://api.twitter.com/1/statuses/mentions.xml"
#define SERVICE_HOME_STATUS_URL    "https://api.twitter.com/1/statuses/home_timeline.xml"
#define SERVICE_USER_STATUS_URL    "https://api.twitter.com/1/statuses/user_timeline/%s.xml"
#define SERVICE_THREAD_STATUS_URL  "https://api.twitter.com/1/statuses/thread_timeline/%s.xml"
#define SERVICE_ACCESS_TOKEN_URL   "https://api.twitter.com/oauth/access_token"
#define SERVICE_STATUS_URL         "http://twitter.com/%s/status/%s"
#define SERVICE_AUTH_URL           "https://twitter.com/oauth/authorize"
#define SERVICE_REQUEST_TOKEN_URL  "http://twitter.com/oauth/request_token"
#define ACCEPT_LETTER_URL          "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789;/?:@&=+$,-_.!~*'%"
#define ACCEPT_LETTER_USER         "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"
#define ACCEPT_LETTER_TAG          "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"
#define ACCEPT_LETTER_REPLY        "1234567890"
#define TOOLTIP_TIMER_SPAN         (1500)
#define RELOAD_TIMER_SPAN          (60*1000)
#define REQUEST_TIMEOUT            (10)
#define SHORTURL_API_URL           "http://is.gd/api.php?longurl=%s"

#define XML_CONTENT(x) (x->children ? (char*) x->children->content : NULL)

typedef struct _PIXBUF_CACHE {
    char* user_id;
    GdkPixbuf* pixbuf;
} PIXBUF_CACHE;

typedef struct _PROCESS_THREAD_INFO {
    GThreadFunc func;
    gboolean processing;
    gpointer data;
    gpointer retval;
} PROCESS_THREAD_INFO;

typedef struct _APPLICATION_INFO {
    char* consumer_key;
    char* consumer_secret;
    char* access_token;
    char* access_token_secret;
    char* font;
} APPLICATION_INFO;

static GdkCursor* hand_cursor = NULL;
static GdkCursor* regular_cursor = NULL;
static GdkCursor* watch_cursor = NULL;
static char* last_condition = NULL;
static int is_processing = FALSE;
static guint reload_timer = 0;
static guint tooltip_timer = 0;
static APPLICATION_INFO application_info = {0};

static void update_timeline(GtkWidget*, gpointer);
static void start_reload_timer(GtkWidget* window);
static void stop_reload_timer(GtkWidget* window);
static void reset_reload_timer(GtkWidget* window);

static gboolean setup_dialog(GtkWidget* window);
static int load_config();
static int save_config();
static gpointer process_thread(gpointer data);

/**
 * sha1/hmac
 */
typedef struct
{
    unsigned long int total[2];
    unsigned long int state[5];
    unsigned char buffer[64];
} sha1_context;

#define GET_UINT32(n,b,i)                       \
{                                               \
    (n) = ( (unsigned long int) (b)[(i)    ] << 24 )       \
        | ( (unsigned long int) (b)[(i) + 1] << 16 )       \
        | ( (unsigned long int) (b)[(i) + 2] <<  8 )       \
        | ( (unsigned long int) (b)[(i) + 3]       );      \
}

#define PUT_UINT32(n,b,i)                       \
{                                               \
    (b)[(i)    ] = (unsigned char) ( (n) >> 24 );       \
    (b)[(i) + 1] = (unsigned char) ( (n) >> 16 );       \
    (b)[(i) + 2] = (unsigned char) ( (n) >>  8 );       \
    (b)[(i) + 3] = (unsigned char) ( (n)       );       \
}

static void sha1_starts(
        sha1_context* ctx)
{
    ctx->total[0] = 0;
    ctx->total[1] = 0;

    ctx->state[0] = 0x67452301;
    ctx->state[1] = 0xEFCDAB89;
    ctx->state[2] = 0x98BADCFE;
    ctx->state[3] = 0x10325476;
    ctx->state[4] = 0xC3D2E1F0;
}

static void sha1_process(
        sha1_context* ctx, const unsigned char data[64])
{
    unsigned long int temp, W[16], A, B, C, D, E;

    GET_UINT32( W[0],  data,  0 );
    GET_UINT32( W[1],  data,  4 );
    GET_UINT32( W[2],  data,  8 );
    GET_UINT32( W[3],  data, 12 );
    GET_UINT32( W[4],  data, 16 );
    GET_UINT32( W[5],  data, 20 );
    GET_UINT32( W[6],  data, 24 );
    GET_UINT32( W[7],  data, 28 );
    GET_UINT32( W[8],  data, 32 );
    GET_UINT32( W[9],  data, 36 );
    GET_UINT32( W[10], data, 40 );
    GET_UINT32( W[11], data, 44 );
    GET_UINT32( W[12], data, 48 );
    GET_UINT32( W[13], data, 52 );
    GET_UINT32( W[14], data, 56 );
    GET_UINT32( W[15], data, 60 );

#define S(x,n) ((x << n) | ((x & 0xFFFFFFFF) >> (32 - n)))

#define R(t)                                            \
    (                                                   \
    temp = W[(t -  3) & 0x0F] ^ W[(t - 8) & 0x0F] ^     \
           W[(t - 14) & 0x0F] ^ W[ t      & 0x0F],      \
    ( W[t & 0x0F] = S(temp,1) )                         \
    )

#define P(a,b,c,d,e,x)                                  \
    {                                                   \
    e += S(a,5) + F(b,c,d) + K + x; b = S(b,30);        \
    }

    A = ctx->state[0];
    B = ctx->state[1];
    C = ctx->state[2];
    D = ctx->state[3];
    E = ctx->state[4];

#define F(x,y,z) (z ^ (x & (y ^ z)))
#define K 0x5A827999

    P( A, B, C, D, E, W[0]  );
    P( E, A, B, C, D, W[1]  );
    P( D, E, A, B, C, W[2]  );
    P( C, D, E, A, B, W[3]  );
    P( B, C, D, E, A, W[4]  );
    P( A, B, C, D, E, W[5]  );
    P( E, A, B, C, D, W[6]  );
    P( D, E, A, B, C, W[7]  );
    P( C, D, E, A, B, W[8]  );
    P( B, C, D, E, A, W[9]  );
    P( A, B, C, D, E, W[10] );
    P( E, A, B, C, D, W[11] );
    P( D, E, A, B, C, W[12] );
    P( C, D, E, A, B, W[13] );
    P( B, C, D, E, A, W[14] );
    P( A, B, C, D, E, W[15] );
    P( E, A, B, C, D, R(16) );
    P( D, E, A, B, C, R(17) );
    P( C, D, E, A, B, R(18) );
    P( B, C, D, E, A, R(19) );

#undef K
#undef F

#define F(x,y,z) (x ^ y ^ z)
#define K 0x6ED9EBA1

    P( A, B, C, D, E, R(20) );
    P( E, A, B, C, D, R(21) );
    P( D, E, A, B, C, R(22) );
    P( C, D, E, A, B, R(23) );
    P( B, C, D, E, A, R(24) );
    P( A, B, C, D, E, R(25) );
    P( E, A, B, C, D, R(26) );
    P( D, E, A, B, C, R(27) );
    P( C, D, E, A, B, R(28) );
    P( B, C, D, E, A, R(29) );
    P( A, B, C, D, E, R(30) );
    P( E, A, B, C, D, R(31) );
    P( D, E, A, B, C, R(32) );
    P( C, D, E, A, B, R(33) );
    P( B, C, D, E, A, R(34) );
    P( A, B, C, D, E, R(35) );
    P( E, A, B, C, D, R(36) );
    P( D, E, A, B, C, R(37) );
    P( C, D, E, A, B, R(38) );
    P( B, C, D, E, A, R(39) );

#undef K
#undef F

#define F(x,y,z) ((x & y) | (z & (x | y)))
#define K 0x8F1BBCDC

    P( A, B, C, D, E, R(40) );
    P( E, A, B, C, D, R(41) );
    P( D, E, A, B, C, R(42) );
    P( C, D, E, A, B, R(43) );
    P( B, C, D, E, A, R(44) );
    P( A, B, C, D, E, R(45) );
    P( E, A, B, C, D, R(46) );
    P( D, E, A, B, C, R(47) );
    P( C, D, E, A, B, R(48) );
    P( B, C, D, E, A, R(49) );
    P( A, B, C, D, E, R(50) );
    P( E, A, B, C, D, R(51) );
    P( D, E, A, B, C, R(52) );
    P( C, D, E, A, B, R(53) );
    P( B, C, D, E, A, R(54) );
    P( A, B, C, D, E, R(55) );
    P( E, A, B, C, D, R(56) );
    P( D, E, A, B, C, R(57) );
    P( C, D, E, A, B, R(58) );
    P( B, C, D, E, A, R(59) );

#undef K
#undef F

#define F(x,y,z) (x ^ y ^ z)
#define K 0xCA62C1D6

    P( A, B, C, D, E, R(60) );
    P( E, A, B, C, D, R(61) );
    P( D, E, A, B, C, R(62) );
    P( C, D, E, A, B, R(63) );
    P( B, C, D, E, A, R(64) );
    P( A, B, C, D, E, R(65) );
    P( E, A, B, C, D, R(66) );
    P( D, E, A, B, C, R(67) );
    P( C, D, E, A, B, R(68) );
    P( B, C, D, E, A, R(69) );
    P( A, B, C, D, E, R(70) );
    P( E, A, B, C, D, R(71) );
    P( D, E, A, B, C, R(72) );
    P( C, D, E, A, B, R(73) );
    P( B, C, D, E, A, R(74) );
    P( A, B, C, D, E, R(75) );
    P( E, A, B, C, D, R(76) );
    P( D, E, A, B, C, R(77) );
    P( C, D, E, A, B, R(78) );
    P( B, C, D, E, A, R(79) );

#undef K
#undef F

    ctx->state[0] += A;
    ctx->state[1] += B;
    ctx->state[2] += C;
    ctx->state[3] += D;
    ctx->state[4] += E;
}

static void sha1_update(
        sha1_context* ctx,
        const unsigned char* input,
        unsigned long int length)
{
    unsigned long int left, fill;

    if (!length)
        return;

    left = ctx->total[0] & 0x3F;
    fill = 64 - left;

    ctx->total[0] += length;
    ctx->total[0] &= 0xFFFFFFFF;

    if (ctx->total[0] < length)
        ctx->total[1]++;

    if (left && length >= fill) {
        memcpy((void*)(ctx->buffer + left), (void*) input, fill);
        sha1_process(ctx, ctx->buffer);
        length -= fill;
        input  += fill;
        left = 0;
    }

    while (length >= 64) {
        sha1_process(ctx, input);
        length -= 64;
        input  += 64;
    }

    if (length)
        memcpy((void*)(ctx->buffer + left), (void *) input, length );
}

static unsigned char sha1_padding[64] =
{
    0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};

static void sha1_finish(
        sha1_context* ctx,
        unsigned char digest[20])
{
    unsigned long int last, padn;
    unsigned long int high, low;
    unsigned char msglen[8];

    high = (ctx->total[0] >> 29)
         | (ctx->total[1] <<  3);
    low  = (ctx->total[0] <<  3);

    PUT_UINT32(high, msglen, 0);
    PUT_UINT32(low,  msglen, 4);

    last = ctx->total[0] & 0x3F;
    padn = (last < 56) ? (56 - last) : (120 - last);

    sha1_update(ctx, sha1_padding, padn);
    sha1_update(ctx, msglen, 8);

    PUT_UINT32(ctx->state[0], digest,  0);
    PUT_UINT32(ctx->state[1], digest,  4);
    PUT_UINT32(ctx->state[2], digest,  8);
    PUT_UINT32(ctx->state[3], digest, 12);
    PUT_UINT32(ctx->state[4], digest, 16);
}

static unsigned char* sha1(
        const unsigned char* input,
        unsigned long int size,
        unsigned char* digest)
{
    sha1_context ctx;
    sha1_starts(&ctx);
    sha1_update(&ctx, input, size);
    sha1_finish(&ctx, digest);
    return digest;
}

static const char hex_table[] = "0123456789abcdef";

static char* to_hex_alloc(const char* input)
{
    unsigned long int i, j, len = strlen(input);
    char* temp = (char*) calloc(len * 2 + 1, sizeof(char));
    for (i = j = 0; i < len; i++) {
        temp[j++] = hex_table[((unsigned char) input[i] & 0xF0) >> 4];
        temp[j++] = hex_table[(unsigned char) input[i]& 0x0F];
    }
    return temp;
}

static const char* base64chars =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz"
    "0123456789+/";
#define is_base64(c) ( \
        isalnum((unsigned char) c) || \
        ((unsigned char) c == '+') || \
        ((unsigned char) c == '/'))

static char* base64encode_alloc(
        const char* input,
        unsigned int size)
{
    int i = 0;
    int j = 0;
    unsigned char char_array_3[3] = {0};
    unsigned char char_array_4[4] = {0};
    char* temp;
    char* ret;

    size = size > 0 ? size : strlen(input);
    ret = temp = (char*) calloc(size * 4 + 1, sizeof(char));
    while (size--) {
        char_array_3[i++] = *(input++);
        if (i == 3) {
            char_array_4[0] =  (char_array_3[0] & 0xfc) >> 2;
            char_array_4[1] = ((char_array_3[0] & 0x03) << 4) + ((char_array_3[1] & 0xf0) >> 4);
            char_array_4[2] = ((char_array_3[1] & 0x0f) << 2) + ((char_array_3[2] & 0xc0) >> 6);
            char_array_4[3] =   char_array_3[2] & 0x3f;

            for (i = 0; i <4; i++)
                *temp++ = base64chars[char_array_4[i]];
            i = 0;
        }
    }

    if (i) {
        for(j = i; j < 3; j++)
            char_array_3[j] = '\0';

        char_array_4[0] =  (char_array_3[0] & 0xfc) >> 2;
        char_array_4[1] = ((char_array_3[0] & 0x03) << 4) + ((char_array_3[1] & 0xf0) >> 4);
        char_array_4[2] = ((char_array_3[1] & 0x0f) << 2) + ((char_array_3[2] & 0xc0) >> 6);
        char_array_4[3] =   char_array_3[2] & 0x3f;

        for (j = 0; (j < i + 1); j++)
            *temp++ = base64chars[char_array_4[j]];

        while((i++ < 3))
            *temp++ = '=';
    }
    *temp = 0;

    return ret;
}

static char* urlencode_alloc(const char* url) {
    unsigned long int i, len = strlen(url);
    char* temp = (char*) calloc(len * 3 + 1, sizeof(char));
    char* ret = temp;
    for (i = 0; i < len; i++) {
        unsigned char c = (unsigned char) url[i];
        if (strchr("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.~-", c))
            *temp++ = c;
        else {
            char buf[3] = {0};
            snprintf(buf, sizeof(buf), "%02x", c);
            *temp++ = '%';
            *temp++ = toupper(buf[0]);
            *temp++ = toupper(buf[1]);
        }
    }
    *temp = 0;

    return ret;
}

static unsigned char* hmac(
        const unsigned char* key,
        unsigned int keylen,
        const unsigned char* data,
        unsigned int datalen,
        unsigned char* digest)
{
    int i;
    sha1_context ctx;
    unsigned char ipad[65] = {0};
    unsigned char opad[65] = {0};
    unsigned char inner[21] = {0};

    memset(ipad, 0, sizeof(ipad));
    memset(opad, 0, sizeof(opad));

    if (keylen > 64) {
        unsigned char keydigest[21];
        sha1_starts(&ctx);
        sha1_update(&ctx, key, keylen);
        sha1_finish(&ctx, keydigest);
        memcpy(ipad, keydigest, 20);
        memcpy(opad, keydigest, 20);
    }
    else {
        memcpy(ipad, key, keylen);
        memcpy(opad, key, keylen);
    }

    for (i = 0; i < 64; i++) {
        ipad[i] ^= 0x36;
        opad[i] ^= 0x5c;
    }

    sha1_starts(&ctx);
    sha1_update(&ctx, ipad, 64);
    sha1_update(&ctx, data, datalen);
    sha1_finish(&ctx, inner);

    sha1_starts(&ctx);
    sha1_update(&ctx, opad, 64);
    sha1_update(&ctx, inner, 20);
    sha1_finish(&ctx, digest);

    return digest;
}

static char*
get_nonce_alloc() {
    char buf[64] = {0};
    char digest[256] = {0};
    snprintf(buf, sizeof(buf), "%d %d", (int) time(NULL), (int) random());
    sha1((const unsigned char*) buf, strlen(buf), (unsigned char*) digest);
    return to_hex_alloc(digest);
}

typedef struct {
    char* data;     // response data from server
    size_t size;    // response size of data
} MEMFILE;

MEMFILE*
memfopen() {
    MEMFILE* mf = (MEMFILE*) malloc(sizeof(MEMFILE));
    if (mf) {
        mf->data = NULL;
        mf->size = 0;
    }
    return mf;
}

void
memfclose(MEMFILE* mf) {
    if (mf->data) free(mf->data);
    free(mf);
}

size_t
memfwrite(char* ptr, size_t size, size_t nmemb, void* stream) {
    MEMFILE* mf = (MEMFILE*) stream;
    int block = size * nmemb;
    if (!mf) return block; // through
    if (!mf->data)
        mf->data = (char*) malloc(block);
    else
        mf->data = (char*) realloc(mf->data, mf->size + block);
    if (mf->data) {
        memcpy(mf->data + mf->size, ptr, block);
        mf->size += block;
    }
    return block;
}

char*
memfstrdup(MEMFILE* mf) {
    char* buf;
    if (mf->size == 0) return NULL;
    buf = (char*) malloc(mf->size + 1);
    memcpy(buf, mf->data, mf->size);
    buf[mf->size] = 0;
    return buf;
}

/**
 * timer register
 */
static guint
reload_timer_func(gpointer data) {
    GtkWidget* window = (GtkWidget*) data;
    gchar* old_data;

    old_data = g_object_get_data(G_OBJECT(window), "last_status_id");
    if (old_data) g_free(old_data);
    g_object_set_data(G_OBJECT(window), "last_status_id", NULL);
    old_data = g_object_get_data(G_OBJECT(window), "page");
    if (old_data) g_free(old_data);
    g_object_set_data(G_OBJECT(window), "page", NULL);

    gdk_threads_enter();
    update_timeline(window, NULL);
    gdk_threads_leave();
    return 0;
}

static void
stop_reload_timer(GtkWidget* window) {
    if (reload_timer != 0) {
        g_source_remove(reload_timer);
        reload_timer = 0;
    }
}

static void
start_reload_timer(GtkWidget* window) {
    stop_reload_timer(window);
    reload_timer = g_timeout_add_full(
            G_PRIORITY_LOW,
            RELOAD_TIMER_SPAN,
            (GSourceFunc) reload_timer_func,
            window,
            NULL);
}

static void
reset_reload_timer(GtkWidget* window) {
    stop_reload_timer(window);
    start_reload_timer(window);
}

/**
 * string utilities
 */
static char* xml_decode_alloc(const char* str) {
    char* buf = NULL;
    unsigned char* pbuf = NULL;
    int len = 0;

    if (!str) return NULL;
    len = strlen(str)*3;
    buf = malloc(len+1);
    memset(buf, 0, len+1);
    pbuf = (unsigned char*) buf;
    while(*str) {
        if (*str == '<') {
            char* ptr = strchr(str, '>');
            if (ptr) str = ptr + 1;
        } else
        if (!memcmp(str, "&amp;", 5)) {
            strcat((char*) pbuf++, "&");
            str += 5;
        } else
        if (!memcmp(str, "&nbsp;", 6)) {
            strcat((char*) pbuf++, " ");
            str += 6;
        } else
        if (!memcmp(str, "&quot;", 6)) {
            strcat((char*) pbuf++, "\"");
            str += 6;
        } else
        if (!memcmp(str, "&nbsp;", 6)) {
            strcat((char*) pbuf++, " ");
            str += 6;
        } else
        if (!memcmp(str, "&lt;", 4)) {
            strcat((char*) pbuf++, "<");
            str += 4;
        } else
        if (!memcmp(str, "&gt;", 4)) {
            strcat((char*) pbuf++, ">");
            str += 4;
        } else
            *pbuf++ = *str++;
    }
    return buf;
}

static char*
get_http_header_alloc(const char* ptr, const char* key) {
    const char* tmp = ptr;

    while (*ptr) {
        tmp = strpbrk(ptr, "\r\n");
        if (!tmp) break;
        if (!strncasecmp(ptr, key, strlen(key)) && *(ptr + strlen(key)) == ':') {
            size_t len;
            char* val;
            const char* top = ptr + strlen(key) + 1;
            while (*top && isspace(*top)) top++;
            if (!*top) return NULL;
            len = tmp - top + 1;
            val = malloc(len);
            memset(val, 0, len);
            strncpy(val, top, len-1);
            return val;
        }
        ptr = tmp + 1;
    }
    return NULL;
}

static char*
get_short_url_alloc(const char* url) {
    gchar* purl;
    CURL* curl;
    MEMFILE* mf; // mem file
    char* ret = NULL;

    purl = g_strdup_printf(SHORTURL_API_URL, url);

    mf = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_URL, purl);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mf);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    curl_easy_perform(curl);
    curl_easy_cleanup(curl);

    g_free(purl);
    ret = memfstrdup(mf);
    memfclose(mf);

    return ret;
}

static char*
get_short_status_alloc(const char* status) {
    const char* ptr = status;
    const char* last = ptr;
    char* ret = NULL;
    int len = 0;
    while(*ptr) {
        if (!strncmp(ptr, "http://", 7) || !strncmp(ptr, "ftp://", 6)) {
            char* link;
            char* short_url;
            const char* tmp;

            if (last != ptr) {
                len += (ptr-last);
                if (!ret) {
                    ret = malloc(len+1);
                    memset(ret, 0, len+1);
                } else ret = realloc(ret, len+1);
                strncat(ret, last, ptr-last);
            }

            tmp = ptr;
            while(*tmp && strchr(ACCEPT_LETTER_URL, *tmp)) tmp++;
            link = malloc(tmp-ptr+1);
            memset(link, 0, tmp-ptr+1);
            memcpy(link, ptr, tmp-ptr);
            short_url = get_short_url_alloc(link);
            if (short_url) {
                free(link);
                link = short_url;
            }

            len += strlen(link);
            if (!ret) {
                ret = malloc(len+1);
                memset(ret, 0, len+1);
            } else ret = realloc(ret, len+1);
            strcat(ret, link);
            free(link);
            ptr = last = tmp;
        } else
            ptr++;
    }
    if (last != ptr) {
        len += (ptr-last);
        if (!ret) {
            ret = malloc(len+1);
            memset(ret, 0, len+1);
        } else ret = realloc(ret, len+1);
        strncat(ret, last, ptr-last);
    }
    return ret;
}

/**
 * oAuth
 */
char*
get_request_token_alloc(
        CURL* curl,
        const char* consumer_key,
        const char* consumer_secret) {

    char* key = NULL;
    char* query = NULL;
    char* nonce;
    char* ptr = NULL;
    char* tmp = NULL;
    char* purl = NULL;
    char auth[21];
    char error[CURL_ERROR_SIZE] = {0};
    MEMFILE* mf; // mem file
    CURLcode res = CURLE_OK;

    nonce = get_nonce_alloc();
    query = g_strdup_printf(
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_request_method=POST"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%d"
        "&oauth_version=1.0",
            consumer_key,
            nonce,
            (int) time(0));
    free(nonce);

    purl = urlencode_alloc(SERVICE_REQUEST_TOKEN_URL);
    ptr = urlencode_alloc(query);
    tmp = g_strdup_printf("POST&%s&%s", purl, ptr);
    free(purl);
    free(ptr);
    key = g_strdup_printf("%s&", consumer_secret);
    hmac((unsigned char*) key, strlen(key),
            (unsigned char*) tmp, strlen(tmp), (unsigned char*) auth);
    g_free(key);
    g_free(tmp);
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    free(tmp);
    tmp = g_strdup_printf("%s&oauth_signature=%s", query, ptr);
    free(ptr);
    g_free(query);
    query = tmp;

    mf = memfopen();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, SERVICE_REQUEST_TOKEN_URL);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_POST, 1);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, query);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mf);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res != CURLE_OK) {
        fputs(error, stderr);
        ptr = NULL;
    } else {
        ptr = memfstrdup(mf);
    }
    g_free(query);
    memfclose(mf);
    return ptr;
}

char*
get_access_token_alloc(
        CURL* curl,
        const char* consumer_key,
        const char* consumer_secret,
        const char* request_token,
        const char* request_token_secret,
        const char* verifier) {

    char* key;
    char* query;
    char* nonce;
    char* ptr = NULL;
    char* tmp;
    char* purl;
    char auth[21];
    char error[CURL_ERROR_SIZE];
    MEMFILE* mf; // mem file
    CURLcode res = CURLE_OK;

    nonce = get_nonce_alloc();
    query = g_strdup_printf(
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_request_method=POST"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%d"
        "&oauth_token=%s"
        "&oauth_token_secret=%s"
        "&oauth_verifier=%s"
        "&oauth_version=1.0",
            consumer_key,
            nonce,
            (int) time(0),
            request_token,
            request_token_secret,
            verifier);
    free(nonce);

    purl = urlencode_alloc(SERVICE_ACCESS_TOKEN_URL);
    ptr = urlencode_alloc(query);
    tmp = g_strdup_printf("POST&%s&%s", purl, ptr);
    free(purl);
    free(ptr);
    key = g_strdup_printf("%s&", consumer_secret);
    hmac((unsigned char*) key, strlen(key),
            (unsigned char*) tmp, strlen(tmp), (unsigned char*) auth);
    g_free(key);
    g_free(tmp);
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    tmp = g_strdup_printf("%s&oauth_signature=%s", query, ptr);
    free(ptr);
    g_free(query);
    query = tmp;

    mf = memfopen();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, SERVICE_ACCESS_TOKEN_URL);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_POST, 1);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, query);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mf);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res != CURLE_OK) {
        fputs(error, stderr);
        ptr = NULL;
    } else {
        ptr = memfstrdup(mf);
    }
    g_free(query);
    memfclose(mf);
    return ptr;
}

/**
 * get pixbuf from URL
 */
static GdkPixbuf* url2pixbuf(const char* url, GError** error) {
    GdkPixbuf* pixbuf = NULL;
    GdkPixbufLoader* loader = NULL;
    GError* _error = NULL;

    if (!strncmp(url, "file:///", 8) || g_file_test(url, G_FILE_TEST_EXISTS)) {
        gchar* newurl = g_filename_from_uri(url, NULL, NULL);
        pixbuf = gdk_pixbuf_new_from_file(newurl ? newurl : url, &_error);
    } else {
        CURL* curl = NULL;
        MEMFILE* mbody;
        MEMFILE* mhead;
        char* head;
        char* body;
        unsigned long size;
        CURLcode res = CURLE_FAILED_INIT;

        curl = curl_easy_init();
        if (!curl) return NULL;

        mbody = memfopen();
        mhead = memfopen();

        curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
        curl_easy_setopt(curl, CURLOPT_URL, url);
        curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
        curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
        curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
        curl_easy_setopt(curl, CURLOPT_WRITEDATA, mbody);
        curl_easy_setopt(curl, CURLOPT_HEADERFUNCTION, memfwrite);
        curl_easy_setopt(curl, CURLOPT_HEADERDATA, mhead);
        curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
        res = curl_easy_perform(curl);
        curl_easy_cleanup(curl);

        head = memfstrdup(mhead);
        memfclose(mhead);
        body = memfstrdup(mbody);
        size = mbody->size;
        memfclose(mbody);

        if (res == CURLE_OK) {
            char* ctype;
            char* csize;
            ctype = get_http_header_alloc(head, "Content-Type");
            csize = get_http_header_alloc(head, "Content-Length");

#ifdef _WIN32
            if (ctype &&
                    (!strcmp(ctype, "image/jpeg") || !strcmp(ctype, "image/gif"))) {
                char temp_path[MAX_PATH];
                char temp_filename[MAX_PATH];
                FILE* fp;
                GetTempPath(sizeof(temp_path), temp_path);
                GetTempFileName(temp_path, "gtktweeter-", 0, temp_filename);
                fp = fopen(temp_filename, "wb");
                if (fp) {
                    fwrite(body, size, 1, fp);
                    fclose(fp);
                }
                pixbuf = gdk_pixbuf_new_from_file(temp_filename, NULL);
                DeleteFile(temp_filename);
            } else
#endif
            {
                if (ctype)
                    loader =
                        (GdkPixbufLoader*) gdk_pixbuf_loader_new_with_mime_type(ctype,
                                error);
                if (csize)
                    size = atol(csize);
                if (!loader) loader = gdk_pixbuf_loader_new();
                if (body && gdk_pixbuf_loader_write(loader, (const guchar*) body,
                            size, &_error)) {
                    pixbuf = gdk_pixbuf_loader_get_pixbuf(loader);
                }
            }
            if (ctype) free(ctype);
            if (csize) free(csize);
            if (loader) gdk_pixbuf_loader_close(loader, NULL);
        } else {
            _error = g_error_new_literal(G_FILE_ERROR, res,
                    curl_easy_strerror(res));
        }

        free(head);
        free(body);
    }

    /* cleanup callback data */
    if (error && _error) *error = _error;
    return pixbuf;
}

/**
 * processing message funcs
 */
static gpointer
process_thread(gpointer data) {
    PROCESS_THREAD_INFO* info = (PROCESS_THREAD_INFO*) data;

    info->retval = info->func(info->data);
    info->processing = FALSE;

    return info->retval;
}

static gpointer
process_func(
        GThreadFunc func, gpointer data,
        GtkWidget* parent, const gchar* message) {
    GtkWidget* loading_image = NULL;
    GtkWidget* loading_label = NULL;
    PROCESS_THREAD_INFO info;
    GError* error = NULL;
    GThread* thread = NULL;

    if (parent) {
        parent = gtk_widget_get_toplevel(parent);
        loading_image = (GtkWidget*) g_object_get_data(G_OBJECT(parent),
                "loading-image");
        if (loading_image) gtk_widget_show(loading_image);

        if (message) {
            loading_label = (GtkWidget*) g_object_get_data(G_OBJECT(parent),
                    "loading-label");
            gtk_label_set_text(GTK_LABEL(loading_label), message);
            gtk_widget_show(loading_label);
        }
    }

    if (parent) gdk_window_set_cursor(parent->window, watch_cursor);
    gdk_flush();

    gdk_threads_leave();

    info.func = func;
    info.data = data;
    info.retval = NULL;
    info.processing = TRUE;
    thread = g_thread_create(
            process_thread,
            &info,
            TRUE,
            &error);
    if (error) g_error_free(error);
    while(info.processing) {
        gdk_threads_enter();
        gtk_main_iteration_do(TRUE);
        gdk_threads_leave();
        g_thread_yield();
    }
    g_thread_join(thread);

    gdk_threads_enter();
    if (loading_image) gtk_widget_hide(loading_image);
    if (loading_label) gtk_widget_hide(loading_label);

    if (parent) gdk_window_set_cursor(parent->window, NULL);
    return info.retval;
}

/**
 * dialog message func
 */
static void
error_dialog(GtkWidget* widget, const char* message) {
    GtkWidget* dialog;
    dialog = gtk_message_dialog_new(
            GTK_WINDOW(gtk_widget_get_toplevel(widget)),
            (GtkDialogFlags)(GTK_DIALOG_MODAL),
            GTK_MESSAGE_WARNING,
            GTK_BUTTONS_CLOSE,
            message, NULL);
    gtk_window_set_title(GTK_WINDOW(dialog), APP_TITLE);
    gtk_widget_show(dialog);
    gtk_window_set_modal(GTK_WINDOW(dialog), TRUE);
    gtk_window_set_position(GTK_WINDOW(dialog), GTK_WIN_POS_CENTER_ON_PARENT);
    gtk_window_set_transient_for(
            GTK_WINDOW(dialog),
            GTK_WINDOW(gtk_widget_get_toplevel(widget)));
    gtk_dialog_run(GTK_DIALOG(dialog));
    gtk_widget_destroy(dialog);
}

static void
insert_status_text(GtkTextBuffer* buffer, GtkTextIter* iter, const char* status) {
    char* ptr = (char*) status;
    char* last = ptr;
    if (!status) return;
    while(*ptr) {
        if (!strncmp(ptr, "http://", 7) || !strncmp(ptr, "ftp://", 6)) {
            GtkTextTag* tag;
            int len;
            char* link;
            char* tmp;
            gchar* url;

            if (last != ptr)
                gtk_text_buffer_insert(buffer, iter, last, ptr-last);

            tmp = ptr;
            while(*tmp && strchr(ACCEPT_LETTER_URL, *tmp)) tmp++;
            len = (int)(tmp-ptr);
            link = malloc(len+1);
            memset(link, 0, len+1);
            strncpy(link, ptr, len);
            tag = gtk_text_buffer_create_tag(
                    buffer,
                    NULL,
                    "foreground",
                    "blue",
                    "underline",
                    PANGO_UNDERLINE_SINGLE,
                    NULL);
            url = g_strdup(link);
            g_object_set_data(G_OBJECT(tag), "url", (gpointer) url);
            gtk_text_buffer_insert_with_tags(buffer, iter, link, -1, tag, NULL);
            free(link);
            ptr = last = tmp;
        } else
        if (*ptr == '@' || !strncmp(ptr, "\xef\xbc\xa0", 3)) {
            GtkTextTag* tag;
            int len;
            char* link;
            char* tmp;
            gchar* url;
            gchar* user_id;
            gchar* user_name;

            if (last != ptr)
                gtk_text_buffer_insert(buffer, iter, last, ptr-last);

            user_name = tmp = ptr + (*ptr == '@' ? 1 : 3);
            while(*tmp && strchr(ACCEPT_LETTER_USER, *tmp)) tmp++;
            len = (int)(tmp-user_name);
            if (len) {
                link = malloc(len+1);
                memset(link, 0, len+1);
                strncpy(link, user_name, len);
                url = g_strdup_printf("@%s", link);
                user_id = g_strdup(link);
                user_name = g_strdup(link);
                free(link);
                tag = gtk_text_buffer_create_tag(
                        buffer,
                        NULL,
                        "foreground",
                        "blue",
                        "underline",
                        PANGO_UNDERLINE_SINGLE,
                        NULL);
                g_object_set_data(G_OBJECT(tag), "user_id", (gpointer) user_id);
                g_object_set_data(G_OBJECT(tag), "user_name", (gpointer) user_name);
                gtk_text_buffer_insert_with_tags(buffer, iter, url, -1, tag, NULL);
                g_free(url);
                ptr = last = tmp;
            } else
                ptr = tmp;
        } else
        if (*ptr == '#') {
            GtkTextTag* tag;
            int len;
            char* link;
            char* tmp;

            if (last != ptr)
                gtk_text_buffer_insert(buffer, iter, last, ptr-last);

            link = tmp = ptr + 1;
            while(*tmp && strchr(ACCEPT_LETTER_TAG, *tmp)) tmp++;
            len = (int)(tmp-link);
            if (len) {
                link = malloc(len+2);
                memset(link, 0, len+2);
                strncpy(link, ptr, len+1);
                tag = gtk_text_buffer_create_tag(
                        buffer,
                        NULL,
                        "foreground",
                        "darkgreen",
                        "underline",
                        PANGO_UNDERLINE_SINGLE,
                        NULL);
                g_object_set_data(G_OBJECT(tag), "tag_name", (gpointer) link);
                gtk_text_buffer_insert_with_tags(buffer, iter, link, -1, tag, NULL);
                ptr = last = tmp;
            } else
                ptr = tmp;
        }
            ptr++;
    }
    if (last != ptr && strlen(last))
        gtk_text_buffer_insert(buffer, iter, last, ptr-last);
}

static time_t
atomtime_to_time(struct tm* tm, char* s) {
    char* os;
    int i;
    struct tm tmptm;
    time_t tmptime;

    static char* wday[] = {
        "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat",
        NULL
    };
    static char* mon[] = {
        "Jan", "Feb", "Mar", "Apr", "May", "Jun",
        "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
        NULL
    };

    memset(&tmptm, 0, sizeof(tmptm));
    os = s;
    /* Sun */
    for(i = 0; i < sizeof(wday)/sizeof(wday[0]); i++) {
        if (strncmp(s, wday[i], strlen(wday[i])) == 0) {
            tmptm.tm_wday = i;
            s += strlen(wday[i]);
            break;
        }
    }
    if (i == sizeof(wday)/sizeof(wday[0])) return -1;
    if (*s != ',' && *s != ' ') return -1;
    while (isspace(*s) || *s == ',') s++;

    /* 25 */
    tmptm.tm_mday = atoi(s);
    while (isdigit(*s)) s++;
    if (*s != ',' && *s != ' ') return -1;
    while (isspace(*s) || *s == ',') s++;

    /* Jan */
    for(i = 0; i < sizeof(mon)/sizeof(mon[0]); i++) {
        if (strncmp(s, mon[i], strlen(mon[i])) == 0) {
            tmptm.tm_mon = i;
            s += strlen(mon[i]);
            break;
        }
    }
    if (i == sizeof(mon)/sizeof(mon[0])) return -1;
    if (*s != ',' && *s != ' ') return -1;
    while (isspace(*s) || *s == ',') s++;

    /* 2002 */
    tmptm.tm_year = atoi(s) - 1900;
    while (isdigit(*s)) s++;
    if (*s != ',' && *s != ' ') return -1;
    while (isspace(*s) || *s == ',') s++;

    /* 00:00:00 */
    if (!(isdigit(s[0]) && isdigit(s[1]) && s[2] == ':'
       && isdigit(s[3]) && isdigit(s[4]) && s[5] == ':'
       && isdigit(s[6]) && isdigit(s[7]) && s[8] == ' ')) return -1;
    tmptm.tm_hour = atoi(s);
    tmptm.tm_min = atoi(s+3);
    tmptm.tm_sec = atoi(s+6);
    if (tmptm.tm_hour >= 24 || tmptm.tm_min >= 60 || tmptm.tm_sec >= 60) return -1;
    while (!isspace(*s) && *s != ',') s++;
    while (isspace(*s) || *s == ',') s++;
    tmptm.tm_isdst = 0;

    tmptm.tm_yday = 0;
    tmptime = mktime(&tmptm) - timezone;
    memcpy(tm, localtime(&tmptime), sizeof(struct tm));
    return mktime(tm);
}

static time_t
tweettime_to_time(struct tm* tm, char* s) {
    char* os;
    int i;
    struct tm tmptm;
    time_t tmptime;

    static char* wday[] = {
        "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat",
        NULL
    };
    static char* mon[] = {
        "Jan", "Feb", "Mar", "Apr", "May", "Jun",
        "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
        NULL
    };

    memset(&tmptm, 0, sizeof(tmptm));
    os = s;
    /* Sun */
    for(i = 0; i < sizeof(wday)/sizeof(wday[0]); i++) {
        if (strncmp(s, wday[i], strlen(wday[i])) == 0) {
            tmptm.tm_wday = i;
            s += strlen(wday[i]);
            break;
        }
    }
    if (i == sizeof(wday)/sizeof(wday[0])) return -1;
    if (*s != ',' && *s != ' ') return -1;
    s++;

    /* Jan */
    for(i = 0; i < sizeof(mon)/sizeof(mon[0]); i++) {
        if (strncmp(s, mon[i], strlen(mon[i])) == 0) {
            tmptm.tm_mon = i;
            s += strlen(mon[i]);
            break;
        }
    }
    if (i == sizeof(mon)/sizeof(mon[0])) return -1;
    if (*s != ',' && *s != ' ') return -1;
    s++;

    /* 25 */
    tmptm.tm_mday = atoi(s);
    while (isdigit(*s)) s++;
    if (*s != ',' && *s != ' ') return -1;
    s++;

    /* 00:00:00 */
    if (!(isdigit(s[0]) && isdigit(s[1]) && s[2] == ':'
       && isdigit(s[3]) && isdigit(s[4]) && s[5] == ':'
       && isdigit(s[6]) && isdigit(s[7]) && s[8] == ' ')) return -1;
    tmptm.tm_hour = atoi(s);
    tmptm.tm_min = atoi(s+3);
    tmptm.tm_sec = atoi(s+6);
    if (tmptm.tm_hour >= 24 || tmptm.tm_min >= 60 || tmptm.tm_sec >= 60) return -1;
    s += 9;

    /* +0000 */
    if (s[0] == '+' || s[1] == '-') s++;
    while (isdigit(*s)) s++;
    if (*s != ',' && *s != ' ') return -1;
    s++;
    tmptm.tm_isdst = 0;

    /* 2002 */
    tmptm.tm_year = atoi(s) - 1900;

    tmptm.tm_yday = 0;
    tmptime = mktime(&tmptm) - timezone;
    memcpy(tm, localtime(&tmptime), sizeof(struct tm));
    return mktime(tm);
}

void
open_url(const gchar* url) {
#ifdef _WIN32
    ShellExecute(NULL, "open", url, NULL, NULL, SW_SHOW);
#else
    int r = 0;
    gchar* command = g_strdup_printf("xdg-open '%s'", url);
    g_spawn_command_line_async(command, NULL);
    g_free(command);
#endif
}

void
clean_condition() {
    if (last_condition) g_free(last_condition);
    last_condition = NULL;
}

void
clean_context(GtkWidget* window) {
    const char* prop_names[] = {
        "mode", "user_id", "user_name", "status_id",
        "last_status_id", "page", "in_reply_to_status_id", "search", "tooltip_data",
        NULL
    };
    const char** prop_name = prop_names;
    while (*prop_name) {
        gchar* prop_data = g_object_get_data(G_OBJECT(window), *prop_name);
        if (prop_data) {
            g_free(prop_data);
            g_object_set_data(G_OBJECT(window), *prop_name, NULL);
        }
        prop_name++;
    }
    g_object_set_data(G_OBJECT(window), "tooltip_data", NULL);
}

/**
 * API limit
 */
static gpointer
check_ratelimit_thread(gpointer data) {
    CURL* curl = NULL;
    CURLcode res = CURLE_OK;
    long http_status = 0;
    struct tm localtm = {0};
    char localdate[256];
    int remaining_hits = 0;

    char* url;
    gpointer result_str = NULL;
    MEMFILE* mbody = NULL;
    char* body = NULL;

    xmlDocPtr doc = NULL;
    xmlNodeSetPtr nodes = NULL;
    xmlXPathContextPtr ctx = NULL;
    xmlXPathObjectPtr path = NULL;
    xmlNodePtr info = NULL;

    url = g_strdup(SERVICE_RATE_LIMIT_URL);

    mbody = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mbody);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_HTTP_CODE, &http_status);
    curl_easy_cleanup(curl);

    g_free(url);

    body = memfstrdup(mbody);
    memfclose(mbody);

    if (res != CURLE_OK) {
        goto leave;
    }
    if (http_status == 304) {
        goto leave;
    }
    if (http_status != 200) {
        goto leave;
    }

    /* parse xml */
    doc = body ? xmlParseDoc((xmlChar*) body) : NULL;
    if (!doc) goto leave;
    ctx = xmlXPathNewContext(doc);
    if (!ctx) goto leave;
    path = xmlXPathEvalExpression((xmlChar*)"/hash", ctx);
    if (!path) goto leave;
    nodes = path->nodesetval;
    if (!nodes || !nodes->nodeTab) goto leave;
    info = nodes->nodeTab[0]->children;
    while(info) {
        if (!strcmp("remaining-hits", (char*) info->name)) {
            remaining_hits = atol(XML_CONTENT(info));
        }
        if (!strcmp("reset-time-in-seconds", (char*) info->name)) {
            long times = atol(XML_CONTENT(info));
            memcpy(&localtm, localtime(&times), sizeof(struct tm));
        }
        info = info->next;
    }

    strftime(localdate, sizeof(localdate), "%x %X", &localtm);
    result_str = g_strdup_printf("%d times before %s", remaining_hits, localdate);

leave:
    if (body) free(body);
    if (path) xmlXPathFreeObject(path);
    if (ctx) xmlXPathFreeContext(ctx);
    if (doc) xmlFreeDoc(doc);
    return result_str;
}

static void
check_ratelimit(GtkWidget* widget, gpointer user_data) {
    gpointer result;
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");
    GtkWidget* statusbar = (GtkWidget*) g_object_get_data(G_OBJECT(window), "statusbar");
    guint context_id = (guint) g_object_get_data(G_OBJECT(statusbar), "context_id");

    if (!application_info.access_token_secret) {
        if (!setup_dialog(window)) return;
    }

    is_processing = TRUE;

    stop_reload_timer(window);
    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);

    gtk_statusbar_pop(GTK_STATUSBAR(statusbar), context_id);
    result = process_func(check_ratelimit_thread, window, window, _("checking ratelimit..."));
    if (result) {
        gtk_statusbar_push(GTK_STATUSBAR(statusbar), context_id, result);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);
    start_reload_timer(window);

    is_processing = FALSE;
}

/**
 * search statuses
 */
static gpointer
search_timeline_thread(gpointer data) {
    GtkWidget* window = (GtkWidget*) data;
    GtkTextBuffer* buffer = NULL;
    CURL* curl = NULL;
    CURLcode res = CURLE_OK;
    long http_status = 0;

    gchar* search = NULL;
    gchar* max_id = NULL;
    gchar* page = NULL;
    gchar* title = NULL;

    char* ptr = NULL;
    char* url;
    char error[CURL_ERROR_SIZE];
    gpointer result_str = NULL;
    MEMFILE* mhead = NULL;
    MEMFILE* mbody = NULL;
    char* body = NULL;
    char* head = NULL;
    int n;
    int length;

    xmlDocPtr doc = NULL;
    xmlNodeSetPtr nodes = NULL;
    xmlXPathContextPtr ctx = NULL;
    xmlXPathObjectPtr path = NULL;

    GtkTextIter iter;

    PIXBUF_CACHE* pixbuf_cache = NULL;

    search = g_object_get_data(G_OBJECT(window), "search");
    ptr = urlencode_alloc(search);
    url = g_strdup_printf("%s?q=%s",
            SERVICE_SEARCH_STATUS_URL,
            ptr);
    free(ptr);

    page = g_object_get_data(G_OBJECT(window), "page");
    if (page) {
        char* tmp = g_strdup_printf("%s&page=%s", url, page);
        g_free(url);
        url = tmp;
    }

    mhead = memfopen();
    mbody = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mbody);
    curl_easy_setopt(curl, CURLOPT_HEADERFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_HEADERDATA, mhead);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_HTTP_CODE, &http_status);
    curl_easy_cleanup(curl);

    g_free(url);
    head = memfstrdup(mhead);
    memfclose(mhead);
    body = memfstrdup(mbody);
    memfclose(mbody);

    if (res != CURLE_OK) {
        result_str = g_strdup(error);
        goto leave;
    }
    if (http_status == 304) {
        goto leave;
    }
    if (http_status != 200) {
        if (body) {
            result_str = xml_decode_alloc(body);
        } else {
            result_str = g_strdup(_("unknown server response"));
        }
        goto leave;
    }

    /* parse xml */
    doc = body ? xmlParseDoc((xmlChar*) body) : NULL;
    if (!doc) {
        if (body)
            result_str = xml_decode_alloc(body);
        else
            result_str = g_strdup(_("unknown server response"));
        goto leave;
    }

    /* create xpath query */
    ctx = xmlXPathNewContext(doc);
    if (!ctx) {
        result_str = g_strdup(_("unknown server response"));
        goto leave;
    }
    path = xmlXPathEvalExpression((xmlChar*)"/rss/channel/item", ctx);
    if (!path) {
        result_str = g_strdup(_("unknown server response"));
        goto leave;
    }
    nodes = path->nodesetval;

    title = g_strdup_printf("%s - Search \"%s\"", APP_TITLE, search);
    gtk_window_set_title(GTK_WINDOW(window), title);
    g_free(title);

    gdk_threads_enter();
    buffer = (GtkTextBuffer*) g_object_get_data(G_OBJECT(window), "buffer");
    if (max_id || page) {
        gtk_text_buffer_get_end_iter(buffer, &iter);
    } else {
        gtk_text_buffer_set_text(buffer, "", 0);
        gtk_text_buffer_get_iter_at_mark(buffer, &iter, gtk_text_buffer_get_insert(buffer));
    }
    gdk_threads_leave();

    /* allocate pixbuf cache buffer */
    length = xmlXPathNodeSetGetLength(nodes);
    pixbuf_cache = malloc(length*sizeof(PIXBUF_CACHE));
    memset(pixbuf_cache, 0, length*sizeof(PIXBUF_CACHE));

    /* make timeline */
    for(n = 0; n < length; n++) {
        char* id = NULL;
        char* user_id = NULL;
        char* icon = NULL;
        char* real = NULL;
        char* user_name = NULL;
        char* text = NULL;
        char* date = NULL;
        int favorited = 0;
        int retweeted = 0;
        GdkPixbuf* pixbuf = NULL;
        GtkTextTag* tag = NULL;
        struct tm localtm;
        char localdate[256];
        int cache;

        /* status nodes */
        xmlNodePtr status = nodes->nodeTab[n];
        if (status->type != XML_ATTRIBUTE_NODE && status->type != XML_ELEMENT_NODE && status->type != XML_CDATA_SECTION_NODE) continue;
        status = status->children;
        while(status) {
            if (!strcmp("guid", (char*) status->name)) {
                char* stop = strrchr((char*) status->children->content, '/');
                if (stop) id = stop + 1;
                else id = (char*) status->children->content;
            }
            if (!strcmp("pubDate", (char*) status->name)) date = (char*) status->children->content;
            if (!strcmp("description", (char*) status->name)) {
                if (status->children) text = (char*) status->children->content;
            }
            if (!strcmp("image_link", (char*) status->name)) {
                if (status->children) icon = (char*) status->children->content;
            }
            if (!strcmp("author", (char*) status->name)) {
                if (status->children) {
                    char* stop;
                    real = user_name = user_id = (char*) status->children->content;
                    stop = strchr(user_id, '@');
                    if (stop) {
                        *stop = 0;
                        stop = strchr(stop + 1, '(');
                        if (stop) {
                            gchar* stop2 = strrchr(stop, ')');
                            if (stop2) {
                                *stop2 = 0;
                                real = stop + 1;
                            }
                        }
                    }
                }
            }
            status = status->next;
        }

        /**
         * avoid to duplicate downloading of icon.
         */
        for(cache = 0; cache < length; cache++) {
            if (!pixbuf_cache[cache].user_id) break;
            if (!strcmp(pixbuf_cache[cache].user_id, user_id)) {
                pixbuf = pixbuf_cache[cache].pixbuf;
                break;
            }
        }
        if (!pixbuf) {
            pixbuf = url2pixbuf((char*) icon, NULL);
            if (pixbuf) {
                pixbuf_cache[cache].user_id = user_id;
                pixbuf_cache[cache].pixbuf = pixbuf;
            }
        }

        /**
         * layout:
         *
         * [icon] [name:name_tag]
         * [message]
         * [date:date_tag]
         *
         */
        gdk_threads_enter();
        if (pixbuf) {
            GdkPixbuf* tmp = gdk_pixbuf_scale_simple(pixbuf, 32, 32, GDK_INTERP_TILES);
            if (tmp) pixbuf = tmp;
            gtk_text_buffer_insert_pixbuf(buffer, &iter, pixbuf);
        }
        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_LARGE,
                "underline",
                PANGO_UNDERLINE_SINGLE,
                "weight",
                PANGO_WEIGHT_BOLD,
                "foreground",
                "#0000FF",
                NULL);
        g_object_set_data(G_OBJECT(tag), "user_id", g_strdup(user_id));
        g_object_set_data(G_OBJECT(tag), "user_name", g_strdup(user_name));
        gtk_text_buffer_insert_with_tags(buffer, &iter, user_name, -1, tag, NULL);
        gtk_text_buffer_insert(buffer, &iter, " (", -1);
        gtk_text_buffer_insert(buffer, &iter, real, -1);
        gtk_text_buffer_insert(buffer, &iter, ")\n", -1);
        text = xml_decode_alloc(text);
        insert_status_text(buffer, &iter, text);
        gtk_text_buffer_insert(buffer, &iter, "\n", -1);

        atomtime_to_time(&localtm, date);
        strftime(localdate, sizeof(localdate), "%x %X", &localtm);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                "#005500",
                NULL);
        g_object_set_data(G_OBJECT(tag), "status_url", g_strdup_printf(SERVICE_STATUS_URL, user_name, id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, localdate, -1, tag, NULL);

        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                "#000055",
                NULL);
        g_object_set_data(G_OBJECT(tag), "reply", g_strdup(user_name));
        g_object_set_data(G_OBJECT(tag), "in_reply_to_status_id", g_strdup(id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, "reply", -1, tag, NULL);

        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                retweeted ? "#555555" : "#000055",
                NULL);
        g_object_set_data(G_OBJECT(tag), "retweet", g_strdup_printf((retweeted ? "-%s" : "%s"), id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, "retweet", -1, tag, NULL);

        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                favorited ? "#555555" : "#000055",
                NULL);
        g_object_set_data(G_OBJECT(tag), "favorite", g_strdup_printf((favorited ? "-%s" : "%s"), id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, "favorite", -1, tag, NULL);

        free(text);
        gtk_text_buffer_insert(buffer, &iter, "\n\n", -1);

        if (n == length - 1) {
            gchar* old_data = g_object_get_data(G_OBJECT(window), "last_status_id");
            if (old_data) g_free(old_data);
            g_object_set_data(G_OBJECT(window), "last_status_id", g_strdup(id));
        }

        gdk_threads_leave();
    }
    free(pixbuf_cache);

    gdk_threads_enter();
    gtk_text_buffer_set_modified(buffer, FALSE) ;
    gtk_text_buffer_get_start_iter(buffer, &iter);
    gtk_text_buffer_place_cursor(buffer, &iter);
    gdk_threads_leave();

leave:
    if (head) free(head);
    if (body) free(body);
    if (path) xmlXPathFreeObject(path);
    if (ctx) xmlXPathFreeContext(ctx);
    if (doc) xmlFreeDoc(doc);
    return result_str;
}

static void
search_timeline(GtkWidget* widget, gpointer user_data) {
    gpointer result;
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");

    if (!application_info.access_token_secret) {
        if (!setup_dialog(window)) return;
    }

    is_processing = TRUE;

    stop_reload_timer(window);
    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);
    result = process_func(search_timeline_thread, window, window, _("searching statuses..."));
    if (result) {
        /* show error message */
        error_dialog(window, result);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);
    start_reload_timer(window);

    is_processing = FALSE;
}

/**
 * update home statuses
 */
static gpointer
update_timeline_thread(gpointer data) {
    GtkWidget* window = (GtkWidget*) data;
    GtkTextBuffer* buffer = NULL;
    CURL* curl = NULL;
    CURLcode res = CURLE_OK;
    struct curl_slist* headers = NULL;
    long http_status = 0;

    gchar* mode = NULL;
    gchar* max_id = NULL;
    gchar* page = NULL;
    gchar* user_id = NULL;
    gchar* user_name = NULL;
    gchar* status_id = NULL;
    gchar* title = NULL;

    char* ptr = NULL;
    char* tmp;
    char* key;
    char* query;
    char* url;
    char* purl;
    char* nonce;
    char auth[21];
    char error[CURL_ERROR_SIZE];
    gpointer result_str = NULL;
    MEMFILE* mhead;
    MEMFILE* mbody;
    char* body;
    char* head;
    int n;
    int length;
    char* cond;

    xmlDocPtr doc = NULL;
    xmlNodeSetPtr nodes = NULL;
    xmlXPathContextPtr ctx = NULL;
    xmlXPathObjectPtr path = NULL;

    GtkTextIter iter;

    PIXBUF_CACHE* pixbuf_cache = NULL;

    mode = g_object_get_data(G_OBJECT(window), "mode");
    if (mode && !strcmp(mode, "replies")) {
        url = g_strdup(SERVICE_REPLIES_STATUS_URL);
    } else {
        user_id = g_object_get_data(G_OBJECT(window), "user_id");
        user_name = g_object_get_data(G_OBJECT(window), "user_name");
        status_id = g_object_get_data(G_OBJECT(window), "status_id");
        if (status_id) {
            url = g_strdup_printf(SERVICE_THREAD_STATUS_URL, status_id);
            /* status_id is temporary value */
            g_free(status_id);
            g_object_set_data(G_OBJECT(window), "status_id", NULL);
        }
        else
        if (user_id)
            url = g_strdup_printf(SERVICE_USER_STATUS_URL, user_id);
        else
            url = g_strdup(SERVICE_HOME_STATUS_URL);
    }

    nonce = get_nonce_alloc();
    query = g_strdup_printf(
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_request_method=GET"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%d"
        "&oauth_token=%s"
        "&oauth_version=1.0",
            application_info.consumer_key,
            nonce,
            (int) time(0),
            application_info.access_token);
    free(nonce);

    max_id = g_object_get_data(G_OBJECT(window), "last_status_id");
    if (max_id) {
        ptr = g_strdup_printf("max_id=%s&%s", max_id, query);
        g_free(query);
        query = ptr;
    } else {
        page = g_object_get_data(G_OBJECT(window), "page");
        if (page) {
            ptr = g_strdup_printf("%s&page=%s", query, page);
            g_free(query);
            query = ptr;
        }
    }

    ptr = g_strdup_printf("include_rts=true&%s", query);
    g_free(query);
    query = ptr;

    purl = urlencode_alloc(url);
    ptr = urlencode_alloc(query);
    tmp = g_strdup_printf("GET&%s&%s", purl, ptr);
    free(purl);
    free(ptr);
    key = g_strdup_printf(
            "%s&%s",
            application_info.consumer_secret,
            application_info.access_token_secret);
    hmac((unsigned char*) key, strlen(key),
            (unsigned char*) tmp, strlen(tmp), (unsigned char*) auth);
    g_free(key);
    g_free(tmp);
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    tmp = g_strdup_printf("%s&oauth_signature=%s", query, ptr);
    free(ptr);
    g_free(query);
    query = tmp;
    purl = g_strdup_printf("%s?%s", url, query);
    g_free(url);
    url = purl;

    mhead = memfopen();
    mbody = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mbody);
    curl_easy_setopt(curl, CURLOPT_HEADERFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_HEADERDATA, mhead);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    if (last_condition) {
        headers = curl_slist_append(headers, last_condition);
        curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
    }
    res = curl_easy_perform(curl);
    if (res == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_HTTP_CODE, &http_status);
	curl_easy_cleanup(curl);

    g_free(query);
    g_free(url);
    head = memfstrdup(mhead);
    memfclose(mhead);
    body = memfstrdup(mbody);
    memfclose(mbody);

    if (res != CURLE_OK) {
        result_str = g_strdup(error);
        goto leave;
    }
    if (http_status == 304) {
        goto leave;
    }
    if (http_status != 200) {
        if (body) {
            result_str = xml_decode_alloc(body);
        } else {
            result_str = g_strdup(_("unknown server response"));
        }
        goto leave;
    }

    cond = get_http_header_alloc(head, "ETag");
    if (cond) {
        clean_condition();
        last_condition = g_strdup_printf("If-None-Match: %s", cond);
    } else {
        cond = get_http_header_alloc(head, "Last-Modified");
        if (cond) {
            clean_condition();
            last_condition = g_strdup_printf("If-None-Match: %s", cond);
        }
    }
    if (cond) free(cond);

    /* parse xml */
    doc = body ? xmlParseDoc((xmlChar*) body) : NULL;
    if (!doc) {
        if (body)
            result_str = xml_decode_alloc(body);
        else
            result_str = g_strdup(_("unknown server response"));
        goto leave;
    }

    /* create xpath query */
    ctx = xmlXPathNewContext(doc);
    if (!ctx) {
        result_str = g_strdup(_("unknown server response"));
        goto leave;
    }
    path = xmlXPathEvalExpression((xmlChar*)"/statuses/status", ctx);
    if (!path) {
        result_str = g_strdup(_("unknown server response"));
        goto leave;
    }
    nodes = path->nodesetval;

    if (mode && !strcmp(mode, "replies"))
        title = g_strdup_printf("%s - Replies", APP_TITLE);
    else
    if (user_name)
        title = g_strdup_printf("%s - %s", APP_TITLE, user_name);
    else
    if (user_id)
        title = g_strdup_printf("%s - (%s)", APP_TITLE, user_id);
    else
        title = g_strdup(APP_TITLE);
    gtk_window_set_title(GTK_WINDOW(window), title);
    g_free(title);

    gdk_threads_enter();
    buffer = (GtkTextBuffer*) g_object_get_data(G_OBJECT(window), "buffer");
    if (max_id || page) {
        gtk_text_buffer_get_end_iter(buffer, &iter);
    } else {
        gtk_text_buffer_set_text(buffer, "", 0);
        gtk_text_buffer_get_iter_at_mark(buffer, &iter, gtk_text_buffer_get_insert(buffer));
    }
    gdk_threads_leave();

    /* allocate pixbuf cache buffer */
    length = xmlXPathNodeSetGetLength(nodes);
    pixbuf_cache = malloc(length*sizeof(PIXBUF_CACHE));
    memset(pixbuf_cache, 0, length*sizeof(PIXBUF_CACHE));

    /* make timeline */
    for(n = 0; n < length; n++) {
        char* id = NULL;
        char* user_id = NULL;
        char* icon = NULL;
        char* real = NULL;
        char* user_name = NULL;
        char* text = NULL;
        char* date = NULL;
        int favorited = 0;
        int retweeted = 0;
        GdkPixbuf* pixbuf = NULL;
        GtkTextTag* tag = NULL;
        struct tm localtm;
        char localdate[256];
        int cache;

        /* status nodes */
        xmlNodePtr status = nodes->nodeTab[n];
        if (status->type != XML_ATTRIBUTE_NODE && status->type != XML_ELEMENT_NODE && status->type != XML_CDATA_SECTION_NODE) continue;
        status = status->children;
        while(status) {
            if (!strcmp("id", (char*) status->name)) id = (char*) status->children->content;
            if (!strcmp("created_at", (char*) status->name)) date = (char*) status->children->content;
            if (!strcmp("text", (char*) status->name)) {
                if (status->children) text = (char*) status->children->content;
            }
            if (!strcmp("favorited", (char*) status->name)) {
                if (!strcmp((char*) status->children->content, "true")) favorited = 1;
            }
            /* user nodes */
            if (!strcmp("user", (char*) status->name)) {
                xmlNodePtr user = status->children;
                while(user) {
                    if (!strcmp("id", (char*) user->name)) user_id = XML_CONTENT(user);
                    if (!strcmp("name", (char*) user->name)) real = XML_CONTENT(user);
                    if (!strcmp("screen_name", (char*) user->name)) user_name = XML_CONTENT(user);
                    if (!strcmp("profile_image_url", (char*) user->name)) {
                        icon = XML_CONTENT(user);
                        icon = (char*) g_strchomp((gchar*) icon);
                        icon = (char*) g_strchug((gchar*) icon);
                    }
                    user = user->next;
                }
            }
            status = status->next;
        }

        /* skip duplicate status in previous/current. */
        if (max_id && !strcmp(id, max_id)) {
            continue;
        }

        /**
         * avoid to duplicate downloading of icon.
         */
        for(cache = 0; cache < length; cache++) {
            if (!pixbuf_cache[cache].user_id) break;
            if (!strcmp(pixbuf_cache[cache].user_id, user_id)) {
                pixbuf = pixbuf_cache[cache].pixbuf;
                break;
            }
        }
        if (!pixbuf) {
            pixbuf = url2pixbuf((char*) icon, NULL);
            if (pixbuf) {
                pixbuf_cache[cache].user_id = user_id;
                pixbuf_cache[cache].pixbuf = pixbuf;
            }
        }

        /**
         * layout:
         *
         * [icon] [name:name_tag]
         * [message]
         * [date:date_tag]
         *
         */
        gdk_threads_enter();
        if (pixbuf) {
            GdkPixbuf* tmp = gdk_pixbuf_scale_simple(pixbuf, 32, 32, GDK_INTERP_TILES);
            if (tmp) pixbuf = tmp;
            gtk_text_buffer_insert_pixbuf(buffer, &iter, pixbuf);
        }
        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_LARGE,
                "underline",
                PANGO_UNDERLINE_SINGLE,
                "weight",
                PANGO_WEIGHT_BOLD,
                "foreground",
                "#0000FF",
                NULL);
        g_object_set_data(G_OBJECT(tag), "user_id", g_strdup(user_id));
        g_object_set_data(G_OBJECT(tag), "user_name", g_strdup(user_name));
        gtk_text_buffer_insert_with_tags(buffer, &iter, user_name, -1, tag, NULL);
        gtk_text_buffer_insert(buffer, &iter, " (", -1);
        gtk_text_buffer_insert(buffer, &iter, real, -1);
        gtk_text_buffer_insert(buffer, &iter, ")\n", -1);
        text = xml_decode_alloc(text);
        insert_status_text(buffer, &iter, text);
        gtk_text_buffer_insert(buffer, &iter, "\n", -1);

        tweettime_to_time(&localtm, date);
        strftime(localdate, sizeof(localdate), "%x %X", &localtm);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                "#005500",
                NULL);
        g_object_set_data(G_OBJECT(tag), "status_url", g_strdup_printf(SERVICE_STATUS_URL, user_name, id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, localdate, -1, tag, NULL);

        // reply
        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                "#000055",
                NULL);
        g_object_set_data(G_OBJECT(tag), "reply", g_strdup(user_name));
        g_object_set_data(G_OBJECT(tag), "in_reply_to_status_id", g_strdup(id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, "reply", -1, tag, NULL);

        // retweet
        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                retweeted ? "#555555" : "#000055",
                NULL);
        g_object_set_data(G_OBJECT(tag), "retweet", g_strdup_printf((retweeted ? "-%s" : "%s"), id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, "retweet", -1, tag, NULL);

        // favorite
        gtk_text_buffer_insert(buffer, &iter, " ", -1);

        tag = gtk_text_buffer_create_tag(
                buffer,
                NULL,
                "scale",
                PANGO_SCALE_X_SMALL,
                "style",
                PANGO_STYLE_ITALIC,
                "foreground",
                favorited ? "#555555" : "#000055",
                NULL);
        g_object_set_data(G_OBJECT(tag), "favorite", g_strdup_printf((favorited ? "-%s" : "%s"), id));
        gtk_text_buffer_insert_with_tags(buffer, &iter, "favorite", -1, tag, NULL);

        free(text);
        gtk_text_buffer_insert(buffer, &iter, "\n\n", -1);

        if (n == length - 1) {
            gchar* old_data = g_object_get_data(G_OBJECT(window), "last_status_id");
            if (old_data) g_free(old_data);
            g_object_set_data(G_OBJECT(window), "last_status_id", g_strdup(id));
        }

        gdk_threads_leave();
    }
    free(pixbuf_cache);

    gdk_threads_enter();
    gtk_text_buffer_set_modified(buffer, FALSE) ;
    gtk_text_buffer_get_start_iter(buffer, &iter);
    gtk_text_buffer_place_cursor(buffer, &iter);
    gdk_threads_leave();

leave:
    if (head) free(head);
    if (body) free(body);
    if (path) xmlXPathFreeObject(path);
    if (ctx) xmlXPathFreeContext(ctx);
    if (doc) xmlFreeDoc(doc);
    return result_str;
}

static void
update_timeline(GtkWidget* widget, gpointer user_data) {
    gpointer result;
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");
    GtkWidget* entry = (GtkWidget*) g_object_get_data(G_OBJECT(window), "entry");

    if (!application_info.access_token_secret) {
        if (!setup_dialog(window)) return;
    }

    is_processing = TRUE;

    stop_reload_timer(window);
    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);
    result = process_func(update_timeline_thread, window, window, _("updating statuses..."));
    if (result) {
        /* show error message */
        error_dialog(window, result);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);
    start_reload_timer(window);

    is_processing = FALSE;

    gtk_widget_grab_focus(entry);
}

static void
home_timeline(GtkWidget* widget, gpointer user_data) {
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    clean_context(window);
    update_timeline(window, NULL);
}

static void
replies_timeline(GtkWidget* widget, gpointer user_data) {
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    clean_context(window);
    g_object_set_data(G_OBJECT(window), "mode", g_strdup("replies"));
    update_timeline(window, NULL);
}

/**
 * retweet status
 */
static gpointer
retweet_status_thread(gpointer data) {
    GtkWidget* window = (GtkWidget*) data;
    CURL* curl = NULL;
    CURLcode res = CURLE_OK;
    long http_status = 0;

    char* status_id = NULL;

    char* ptr = NULL;
    char* tmp;
    char* key;
    char* query;
    char* nonce;
    char* url;
    char* purl;
    char auth[21];
    char error[CURL_ERROR_SIZE];
    gpointer result_str = NULL;
    MEMFILE* mbody;
    char* body;

    gdk_threads_enter();
    status_id = g_object_get_data(G_OBJECT(window), "retweet");
    gdk_threads_leave();

    if (!status_id || strlen(status_id) == 0) return NULL;
    url = g_strdup_printf(SERVICE_RETWEET_URL, status_id);

    nonce = get_nonce_alloc();
    query = g_strdup_printf(
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_request_method=POST"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%d"
        "&oauth_token=%s"
        "&oauth_version=1.0",
            application_info.consumer_key,
            nonce,
            (int) time(0),
            application_info.access_token);
    free(nonce);

    purl = urlencode_alloc(url);
    ptr = urlencode_alloc(query);
    tmp = g_strdup_printf("POST&%s&%s", purl, ptr);
    free(purl);
    free(ptr);
    key = g_strdup_printf(
            "%s&%s",
            application_info.consumer_secret,
            application_info.access_token_secret);
    hmac((unsigned char*) key, strlen(key),
            (unsigned char*) tmp, strlen(tmp), (unsigned char*) auth);
    g_free(key);
    g_free(tmp);
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    free(tmp);
    tmp = g_strdup_printf("%s&oauth_signature=%s", query, ptr);
    free(ptr);
    g_free(query);
    query = tmp;

    mbody = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_POST, 1);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, query);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mbody);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_HTTP_CODE, &http_status);
    curl_easy_cleanup(curl);

    g_free(query);
    body = memfstrdup(mbody);
    memfclose(mbody);
    if (http_status != 200) {
        if (body) {
            result_str = xml_decode_alloc(body);
        } else {
            result_str = g_strdup(_("unknown server response"));
        }
        goto leave;
    }

leave:
    if (body) free(body);
    return result_str;
}

static void
retweet_status(GtkWidget* widget, GtkTextTag* tag) {
    gchar* status_id;
    gpointer result;
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");

    is_processing = TRUE;

    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);
    status_id = g_object_get_data(G_OBJECT(tag), "retweet");
    g_object_set_data(G_OBJECT(window), "retweet", (gchar*) status_id);
    result = process_func(retweet_status_thread, window, window, _("retweeting status..."));
    g_object_set_data(G_OBJECT(window), "retweet", NULL);
    if (!result) {
        GValue gval = {0};
        int retweeted = (*status_id != '-');
        g_value_init(&gval, G_TYPE_STRING);
        g_value_set_string(&gval, retweeted ? "#555555" : "#000055");
        g_object_set_property(G_OBJECT(tag), "foreground", &gval);
        if (retweeted)
            g_object_set_data(G_OBJECT(tag), "retweet", g_strdup_printf("-%s", status_id));
        else
            g_object_set_data(G_OBJECT(tag), "retweet", g_strdup(status_id+1));
        g_free(status_id);

        clean_condition();
    }
    if (result) {
        /* show error message */
        error_dialog(window, result);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);

    is_processing = FALSE;

    update_timeline(window, NULL);
}

/**
 * user profile
 */
static gpointer
user_profile_thread(gpointer data) {
    CURL* curl = NULL;
    char* ptr = NULL;
    char* tmp;
    char* key;
    char* query;
    char* url;
    char* purl;
    char* nonce;
    char auth[21];
    gpointer result_str = NULL;
    MEMFILE* mf;
    char* body;
    int n;
    int length;

    xmlDocPtr doc = NULL;
    xmlNodeSetPtr nodes = NULL;
    xmlXPathContextPtr ctx = NULL;
    xmlXPathObjectPtr path = NULL;

    url = g_strdup_printf(SERVICE_USER_SHOW_URL, (gchar*) data);

    nonce = get_nonce_alloc();
    query = g_strdup_printf(
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_request_method=GET"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%d"
        "&oauth_token=%s"
        "&oauth_version=1.0",
            application_info.consumer_key,
            nonce,
            (int) time(0),
            application_info.access_token);
    free(nonce);

    purl = urlencode_alloc(url);
    ptr = urlencode_alloc(query);
    tmp = g_strdup_printf("GET&%s&%s", purl, ptr);
    free(purl);
    free(ptr);
    key = g_strdup_printf(
            "%s&%s",
            application_info.consumer_secret,
            application_info.access_token_secret);
    hmac((unsigned char*) key, strlen(key),
            (unsigned char*) tmp, strlen(tmp), (unsigned char*) auth);
    g_free(key);
    g_free(tmp);
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    tmp = g_strdup_printf("%s&oauth_signature=%s", query, ptr);
    free(ptr);
    g_free(query);
    query = tmp;
    purl = g_strdup_printf("%s?%s", url, query);
    g_free(url);
    url = purl;

    mf = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mf);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    curl_easy_perform(curl);
    curl_easy_cleanup(curl);

    g_free(query);
    g_free(url);
    body = memfstrdup(mf);
    memfclose(mf);

    doc = body ? xmlParseDoc((xmlChar*) body) : NULL;
    if (!doc) goto leave;
    ctx = xmlXPathNewContext(doc);
    if (!ctx) goto leave;
    path = xmlXPathEvalExpression((xmlChar*)"/user", ctx);
    if (!path) goto leave;
    nodes = path->nodesetval;

    length = xmlXPathNodeSetGetLength(nodes);

    result_str = g_strdup("");

    /* make timeline */
    for(n = 0; n < length; n++) {
        xmlNodePtr info = nodes->nodeTab[n];
        if (info->type != XML_ATTRIBUTE_NODE && info->type != XML_ELEMENT_NODE && info->type != XML_CDATA_SECTION_NODE) continue;
        info = info->children;
        while(info) {
            // <protected>
            // <friends_count>
            // <followers_count>
            if (!strcmp("name", (char*) info->name)) {
                tmp = g_strconcat(result_str, "user name:", XML_CONTENT(info), "\n", NULL);
                g_free(result_str);
                result_str = tmp;
            }
            if (!strcmp("screen_name", (char*) info->name)) {
                tmp = g_strconcat(result_str, "screen name:", XML_CONTENT(info), "\n", NULL);
                g_free(result_str);
                result_str = tmp;
            }
            if (!strcmp("description", (char*) info->name)) {
                tmp = g_strconcat(result_str, "description:\n", XML_CONTENT(info), "\n\n", NULL);
                g_free(result_str);
                result_str = tmp;
            }
            if (!strcmp("location", (char*) info->name)) {
                tmp = g_strconcat(result_str, "location:", XML_CONTENT(info), "\n", NULL);
                g_free(result_str);
                result_str = tmp;
            }
            if (!strcmp("url", (char*) info->name)) {
                tmp = g_strconcat(result_str, "URL:", XML_CONTENT(info), "\n", NULL);
                g_free(result_str);
                result_str = tmp;
            }
            info = info->next;
        }
    }

leave:
    if (body) free(body);
    if (path) xmlXPathFreeObject(path);
    if (ctx) xmlXPathFreeContext(ctx);
    if (doc) xmlFreeDoc(doc);
    return result_str;
}

static void
user_profile(GtkWidget* widget, gchar* url) {
    gpointer result;
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");
    GtkTooltips* tooltips = (GtkTooltips*) g_object_get_data(G_OBJECT(window), "tooltips");

    is_processing = TRUE;

    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);
    result = process_func(user_profile_thread, url, window, _("getting profile..."));
    if (result) {
        gtk_tooltips_set_tip(
                GTK_TOOLTIPS(tooltips),
                textview,
                result, url);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);

    is_processing = FALSE;
}

/**
 * expand short url
 */
static gpointer
expand_short_url_thread(gpointer data) {
    CURL* curl = NULL;
    gpointer result_str = NULL;
    MEMFILE* mf;
    char* head;

    mf = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_VERBOSE, 0);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_URL, (gchar*) data);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_HEADERFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_HEADERDATA, mf);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, NULL);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 0);
    curl_easy_perform(curl);
    curl_easy_cleanup(curl);

    head = memfstrdup(mf);
    memfclose(mf);
    result_str = get_http_header_alloc(head, "Location");
    free(head);

    return result_str;
}

static void
expand_short_url(GtkWidget* widget, gchar* url) {
    gpointer result;
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");
    GtkTooltips* tooltips = (GtkTooltips*) g_object_get_data(G_OBJECT(window), "tooltips");

    is_processing = TRUE;

    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);
    result = process_func(expand_short_url_thread, url, window, _("expanding URL..."));
    if (result) {
        gtk_tooltips_set_tip(
                GTK_TOOLTIPS(tooltips),
                textview,
                result, url);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);

    is_processing = FALSE;
}

/**
 * favorite status
 */
static gpointer
favorite_status_thread(gpointer data) {
    GtkWidget* window = (GtkWidget*) data;
    CURL* curl = NULL;
    CURLcode res = CURLE_OK;
    long http_status = 0;

    char* ptr = NULL;
    char* tmp;
    char* status_id = NULL;
    char* key;
    char* query;
    char* nonce;
    char* url;
    char* purl;
    char auth[21];
    char error[CURL_ERROR_SIZE];
    gpointer result_str = NULL;
    MEMFILE* mbody;
    char* body;

    gdk_threads_enter();
    status_id = g_object_get_data(G_OBJECT(window), "favorite");
    gdk_threads_leave();

    if (!status_id || strlen(status_id) == 0) return NULL;
    if (*status_id == '-') {
        url = g_strdup_printf(SERVICE_UNFAVORITE_URL, status_id+1);
    } else {
        url = g_strdup_printf(SERVICE_FAVORITE_URL, status_id);
    }

    nonce = get_nonce_alloc();
    query = g_strdup_printf(
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_request_method=POST"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%d"
        "&oauth_token=%s"
        "&oauth_version=1.0",
            application_info.consumer_key,
            nonce,
            (int) time(0),
            application_info.access_token);
    free(nonce);

    purl = urlencode_alloc(url);
    ptr = urlencode_alloc(query);
    tmp = g_strdup_printf("POST&%s&%s", purl, ptr);
    free(purl);
    free(ptr);
    key = g_strdup_printf(
            "%s&%s",
            application_info.consumer_secret,
            application_info.access_token_secret);
    hmac((unsigned char*) key, strlen(key),
            (unsigned char*) tmp, strlen(tmp), (unsigned char*) auth);
    g_free(key);
    g_free(tmp);
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    free(tmp);
    tmp = g_strdup_printf("%s&oauth_signature=%s", query, ptr);
    free(ptr);
    g_free(query);
    query = tmp;

    mbody = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_POST, 1);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, query);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mbody);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_HTTP_CODE, &http_status);
    curl_easy_cleanup(curl);

    g_free(query);
    body = memfstrdup(mbody);

    if (http_status != 200) {
        if (body) {
            result_str = xml_decode_alloc(body);
        } else {
            result_str = g_strdup(_("unknown server response"));
        }
        goto leave;
    }

leave:
    if (body) free(body);
    return result_str;
}

static void
favorite_status(GtkWidget* widget, GtkTextTag* tag) {
    gchar* status_id;
    gpointer result;
    GtkWidget* window = (GtkWidget*) gtk_widget_get_toplevel(widget);
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");

    is_processing = TRUE;

    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);
    status_id = g_object_get_data(G_OBJECT(tag), "favorite");
    g_object_set_data(G_OBJECT(window), "favorite", (gchar*) status_id);
    result = process_func(favorite_status_thread, window, window, _("favoriting status..."));
    g_object_set_data(G_OBJECT(window), "favorite", NULL);
    if (!result) {
        GValue gval = {0};
        int favorited = (*status_id != '-');
        g_value_init(&gval, G_TYPE_STRING);
        g_value_set_string(&gval, favorited ? "#555555" : "#000055");
        g_object_set_property(G_OBJECT(tag), "foreground", &gval);
        if (favorited)
            g_object_set_data(G_OBJECT(tag), "favorite", g_strdup_printf("-%s", status_id));
        else
            g_object_set_data(G_OBJECT(tag), "favorite", g_strdup(status_id+1));
        g_free(status_id);

        clean_condition();
    }
    if (result) {
        /* show error message */
        error_dialog(window, result);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);

    is_processing = FALSE;
}

/**
 * post my status
 */
static gpointer
post_status_thread(gpointer data) {
    GtkWidget* window = (GtkWidget*) data;
    GtkWidget* entry = NULL;
    CURL* curl = NULL;
    CURLcode res = CURLE_OK;
    long http_status = 0;

    gchar* in_reply_to_status_id = NULL;
    char* ptr = NULL;
    char* tmp;
    char* status = NULL;
    char* status_encoded;
    char* key;
    char* query;
    char* nonce;
    char* purl;
    char auth[21];
    char error[CURL_ERROR_SIZE];
    gpointer result_str = NULL;
    MEMFILE* mbody;
    char* body = NULL;

    gdk_threads_enter();
    entry = (GtkWidget*) g_object_get_data(G_OBJECT(window), "entry");
    status = (char*) gtk_entry_get_text(GTK_ENTRY(entry));
    gdk_threads_leave();

    if (!status || strlen(status) == 0) return NULL;

    ptr = get_short_status_alloc(status);
    if (!ptr) ptr = strdup(status);
    status_encoded = urlencode_alloc(ptr);
    free(ptr);

    nonce = get_nonce_alloc();
    query = g_strdup_printf(
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_request_method=POST"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%d"
        "&oauth_token=%s"
        "&oauth_version=1.0"
        "&status=%s",
            application_info.consumer_key,
            nonce,
            (int) time(0),
            application_info.access_token,
            status_encoded);
    free(nonce);
    free(status_encoded);

    in_reply_to_status_id = g_object_get_data(G_OBJECT(window), "in_reply_to_status_id");
    if (in_reply_to_status_id) {
        tmp = g_strdup_printf("in_reply_to_status_id=%s&%s", in_reply_to_status_id, query);
        g_free(query);
        query = tmp;
    }

    purl = urlencode_alloc(SERVICE_UPDATE_URL);
    ptr = urlencode_alloc(query);
    tmp = g_strdup_printf("POST&%s&%s", purl, ptr);
    free(purl);
    free(ptr);
    key = g_strdup_printf(
            "%s&%s",
            application_info.consumer_secret,
            application_info.access_token_secret);
    hmac((unsigned char*) key, strlen(key),
            (unsigned char*) tmp, strlen(tmp), (unsigned char*) auth);
    g_free(key);
    g_free(tmp);
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    free(tmp);
    tmp = g_strdup_printf("%s&oauth_signature=%s", query, ptr);
    free(ptr);
    g_free(query);
    query = tmp;

    mbody = memfopen();
    curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, SERVICE_UPDATE_URL);
    curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, REQUEST_TIMEOUT);
    curl_easy_setopt(curl, CURLOPT_POST, 1);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, query);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mbody);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_HTTP_CODE, &http_status);
    if (http_status == 417) {
        struct curl_slist* headers = NULL;
        headers = curl_slist_append(headers, "Expect: ");
        curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
        res = curl_easy_perform(curl);
        curl_slist_free_all(headers);
        if (res == CURLE_OK)
            curl_easy_getinfo(curl, CURLINFO_HTTP_CODE, &http_status);
    }
    curl_easy_cleanup(curl);

    g_free(query);
    body = memfstrdup(mbody);
    memfclose(mbody);
    if (res != CURLE_OK) {
        result_str = g_strdup(error);
        goto leave;
    }
    if (http_status != 200) {
        if (body) {
            result_str = xml_decode_alloc(body);
        } else {
            result_str = g_strdup(_("unknown server response"));
        }
        goto leave;
    } else {
        /* succeeded to the post */
        gdk_threads_enter();
        gtk_entry_set_text(GTK_ENTRY(entry), "");
        gdk_threads_leave();
    }

leave:
    if (body) free(body);
    return result_str;
}

static void
post_status(GtkWidget* widget, gpointer user_data) {
    gpointer result;
    GtkWidget* window = (GtkWidget*) user_data;
    GtkWidget* textview = (GtkWidget*) g_object_get_data(G_OBJECT(window), "textview");
    GtkWidget* toolbox = (GtkWidget*) g_object_get_data(G_OBJECT(window), "toolbox");

    if (!application_info.access_token_secret) {
        if (!setup_dialog(window)) return;
    }

    is_processing = TRUE;

    /* disable toolbox */
    gtk_widget_set_sensitive(toolbox, FALSE);
    /* set watch cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            watch_cursor);
    result = process_func(post_status_thread, window, window, _("posting status..."));
    if (!result) {
        clean_condition();
        clean_context(window);
        result = process_func(update_timeline_thread, window, window, _("updating statuses..."));
    }
    if (result) {
        /* show error message */
        error_dialog(window, result);
        g_free(result);
    }
    /* enable toolbox */
    gtk_widget_set_sensitive(toolbox, TRUE);
    /* set regular cursor at textview */
    gdk_window_set_cursor(
            gtk_text_view_get_window(
                GTK_TEXT_VIEW(textview),
                GTK_TEXT_WINDOW_TEXT),
            regular_cursor);

    is_processing = FALSE;
}

/**
 * reload button
 */
static void
on_reload_clicked(GtkWidget* widget, gpointer user_data) {
    GtkWidget* window = gtk_widget_get_toplevel(widget);
    gchar* mode = g_object_get_data(G_OBJECT(window), "mode");
    clean_condition();
    if (mode && !strcmp(mode, "search")) {
        search_timeline(window, NULL);
    } else {
        update_timeline(window, NULL);
    }
}

/**
 * enter key handler
 */
static gboolean
on_entry_activate(GtkWidget* widget, gpointer user_data) {
    GtkWidget* window = gtk_widget_get_toplevel(widget);
    char* message = (char*) gtk_entry_get_text(GTK_ENTRY(widget));

    if (is_processing) return FALSE;
    if (!message || strlen(message) == 0) return FALSE;
    stop_reload_timer(window);
    post_status(widget, user_data);
    start_reload_timer(window);
    return FALSE;
}

/**
 * search box
 */
static void
on_search_word_activate(GtkWidget* widget, gpointer user_data) {
    GtkDialog* dialog = (GtkDialog*) user_data;
    gtk_dialog_response(dialog, GTK_RESPONSE_OK);
}

static void
search_dialog(GtkWidget* widget, gpointer user_data) {
    GtkWidget* window = gtk_widget_get_toplevel(widget);
    GtkWidget* dialog = NULL;
    GtkWidget* label = NULL;
    GtkWidget* entry = NULL;
    gchar* word = NULL;
    gint ret;

    /* login dialog */
    dialog = gtk_dialog_new();
    gtk_dialog_add_buttons(GTK_DIALOG(dialog),
            GTK_STOCK_OK, GTK_RESPONSE_OK,
            GTK_STOCK_CANCEL, GTK_RESPONSE_CANCEL,
            NULL);
    gtk_dialog_set_default_response(GTK_DIALOG(dialog), GTK_RESPONSE_OK);

    gtk_window_set_title(GTK_WINDOW(dialog), _(APP_TITLE" Search"));

    /* word */
    label = gtk_label_new(_("Search _Word:"));
    gtk_label_set_use_underline(GTK_LABEL(label), TRUE);
    gtk_misc_set_alignment(GTK_MISC(label), 0.0f, 0.5f);
    gtk_box_pack_start (GTK_BOX (GTK_DIALOG(dialog)->vbox), label, TRUE, TRUE, 0);

    entry = gtk_entry_new();
    gtk_label_set_mnemonic_widget(GTK_LABEL(label), entry);
    g_signal_connect(G_OBJECT(entry), "activate", G_CALLBACK(on_search_word_activate), dialog);
    gtk_box_pack_start (GTK_BOX (GTK_DIALOG(dialog)->vbox), entry, TRUE, TRUE, 0);

    /* show modal dialog */
    gtk_window_set_modal(GTK_WINDOW(dialog), TRUE);
    gtk_window_set_transient_for(
            GTK_WINDOW(dialog),
            GTK_WINDOW(window));
    gtk_window_set_position(GTK_WINDOW(dialog), GTK_WIN_POS_CENTER_ON_PARENT);
    gtk_widget_show_all(dialog);

    ret = gtk_dialog_run(GTK_DIALOG(dialog));
    word = g_strdup(gtk_entry_get_text(GTK_ENTRY(entry)));
    gtk_widget_destroy(dialog);

    if (ret == GTK_RESPONSE_OK) {
        clean_condition();
        clean_context(window);
        g_object_set_data(G_OBJECT(window), "mode", g_strdup("search"));
        g_object_set_data(G_OBJECT(window), "search", g_strdup(word));
        search_timeline(window, NULL);
    }
    g_free(word);
}

/**
 * login dialog func
 */
static gboolean
setup_dialog(GtkWidget* window) {
    GtkWidget* dialog = NULL;
    GtkWidget* label = NULL;
    GtkWidget* pin = NULL;
    gboolean ret = FALSE;
    CURL* curl;
    char* ptr;
    char* tmp;
    const char* request_token = NULL;
    const char* request_token_secret = NULL;

    /* login dialog */
    dialog = gtk_dialog_new();
    gtk_dialog_add_buttons(GTK_DIALOG(dialog),
            GTK_STOCK_OK, GTK_RESPONSE_OK,
            GTK_STOCK_CANCEL, GTK_RESPONSE_CANCEL,
            NULL);
    gtk_dialog_set_default_response(GTK_DIALOG(dialog), GTK_RESPONSE_OK);

    gtk_window_set_title(GTK_WINDOW(dialog), _(APP_TITLE" Setup"));

    /* pin */
    label = gtk_label_new(_("_PIN Code:"));
    gtk_label_set_use_underline(GTK_LABEL(label), TRUE);
    gtk_misc_set_alignment(GTK_MISC(label), 0.0f, 0.5f);
    gtk_box_pack_start (GTK_BOX (GTK_DIALOG(dialog)->vbox), label, TRUE, TRUE, 0);

    pin = gtk_entry_new();
    gtk_label_set_mnemonic_widget(GTK_LABEL(label), pin);
    gtk_box_pack_start (GTK_BOX (GTK_DIALOG(dialog)->vbox), pin, TRUE, TRUE, 0);

    /* show modal dialog */
    gtk_window_set_modal(GTK_WINDOW(dialog), TRUE);
    gtk_window_set_transient_for(
            GTK_WINDOW(dialog),
            GTK_WINDOW(window));
    gtk_window_set_position(GTK_WINDOW(dialog), GTK_WIN_POS_CENTER_ON_PARENT);
    gtk_widget_show_all(dialog);

    curl = curl_easy_init();
    ptr = get_request_token_alloc(
            curl,
            application_info.consumer_key,
            application_info.consumer_secret);
    curl_easy_cleanup(curl);

    // parse response parameters
    tmp = ptr;
    while (tmp && *tmp) {
        char* stop = strchr(tmp, '&');
        if (stop) {
            *stop = 0;
            if (!strncmp(tmp, "oauth_token=", 12)) {
                request_token = strdup(tmp + 12);
            }
            if (!strncmp(tmp, "oauth_token_secret=", 19)) {
                request_token_secret = strdup(tmp + 19);
            }
            tmp = stop + 1;
        } else
            break;
    }
    free(ptr);

    if (!request_token || !request_token_secret) {
        return -1;
    }

    ptr = g_strdup_printf("%s?oauth_token=%s",
            SERVICE_AUTH_URL, request_token);
    open_url(ptr);

    if (gtk_dialog_run(GTK_DIALOG(dialog)) == GTK_RESPONSE_OK) {
        /* set mail/pass value to window object */
        char* pin_code = (char*) gtk_entry_get_text(GTK_ENTRY(pin));

        // parse response parameters
        tmp = ptr;
        while (tmp && *tmp) {
            char* stop = strchr(tmp, '&');
            if (stop) {
                *stop = 0;
                if (!strncmp(tmp, "oauth_token=", 12)) {
                    request_token = strdup(tmp + 12);
                }
                if (!strncmp(tmp, "oauth_token_secret=", 19)) {
                    request_token_secret = strdup(tmp + 19);
                }
                tmp = stop + 1;
            } else
                break;
        }
        free(ptr);

        ptr = get_access_token_alloc(
                curl,
                application_info.consumer_key,
                application_info.consumer_secret,
                request_token,
                request_token_secret,
                pin_code);
        tmp = ptr;
        if (application_info.access_token) {
            free(application_info.access_token);
            application_info.access_token = NULL;
        }
        if (application_info.access_token_secret) {
            free(application_info.access_token_secret);
            application_info.access_token_secret = NULL;
        }
        while (tmp && *tmp) {
            char* stop = strchr(tmp, '&');
            if (stop) {
                *stop = 0;
                if (!strncmp(tmp, "oauth_token=", 12)) {
                    application_info.access_token = strdup(tmp + 12);
                }
                if (!strncmp(tmp, "oauth_token_secret=", 19)) {
                    application_info.access_token_secret = strdup(tmp + 19);
                }
                tmp = stop + 1;
            } else
                break;
        }

        save_config();
        ret = TRUE;
    }

    gtk_widget_destroy(dialog);
    return ret;
}

static guint
tooltip_timer_func(gpointer data) {
    GtkWidget* window = (GtkWidget*) data;
    gchar* tooltip_data;

    tooltip_data = g_object_get_data(G_OBJECT(window), "tooltip_data");
    if (!tooltip_data) return 0;

    gdk_threads_enter();
    if (!strncmp(tooltip_data, "url:", 4)) {
        expand_short_url(window, tooltip_data+4);
    }
    if (!strncmp(tooltip_data, "user:", 5)) {
        user_profile(window, tooltip_data+5);
    }
    gdk_threads_leave();
    return 0;
}

static void
textview_change_cursor(GtkWidget* textview, gint x, gint y) {
    static gboolean hovering_over_link = FALSE;
    GtkWidget* window = gtk_widget_get_toplevel(textview);
    GSList* tags = NULL;
    GtkTextBuffer* buffer;
    GtkTextIter iter;
    GtkTooltips* tooltips = NULL;
    gboolean hovering = FALSE;
    gchar* user_id = NULL;
    gchar* short_url = NULL;
    int len, n;

    if (is_processing) {
        return;
    }

    buffer = gtk_text_view_get_buffer(GTK_TEXT_VIEW(textview));
    gtk_text_view_get_iter_at_location(GTK_TEXT_VIEW(textview), &iter, x, y);
    tooltips = (GtkTooltips*) g_object_get_data(G_OBJECT(window), "tooltips");

    tags = gtk_text_iter_get_tags(&iter);
    if (tags) {
        len = g_slist_length(tags);
        for(n = 0; n < len; n++) {
            GtkTextTag* tag = (GtkTextTag*) g_slist_nth_data(tags, n);
            if (tag) {
                if (g_object_get_data(G_OBJECT(tag), "url")) {
                    hovering = TRUE;
                    short_url = g_object_get_data(G_OBJECT(tag), "url");
                    g_object_set_data(G_OBJECT(window), "tooltip_data", g_strdup_printf("url:%s", short_url));
                    break;
                }
                if (g_object_get_data(G_OBJECT(tag), "user_id")) {
                    hovering = TRUE;
                    user_id = g_object_get_data(G_OBJECT(tag), "user_id");
                    g_object_set_data(G_OBJECT(window), "tooltip_data", g_strdup_printf("user:%s", user_id));
                    break;
                }
                if (   g_object_get_data(G_OBJECT(tag), "status_url")
                    || g_object_get_data(G_OBJECT(tag), "retweet")
                    || g_object_get_data(G_OBJECT(tag), "reply")
                    || g_object_get_data(G_OBJECT(tag), "favorite")
                    || g_object_get_data(G_OBJECT(tag), "tag_name")) {
                    hovering = TRUE;
                    break;
                }
            }
        }
        g_slist_free(tags);
    }
    if (hovering != hovering_over_link) {
        hovering_over_link = hovering;
        gdk_window_set_cursor(
                gtk_text_view_get_window(
                    GTK_TEXT_VIEW(textview),
                    GTK_TEXT_WINDOW_TEXT),
                hovering_over_link ? hand_cursor : regular_cursor);

        if (hovering_over_link) {
            tooltip_timer = g_timeout_add_full(
                    G_PRIORITY_LOW,
                    TOOLTIP_TIMER_SPAN,
                    (GSourceFunc) tooltip_timer_func,
                    window,
                    NULL);
        } else {
            gchar* old_data = g_object_get_data(G_OBJECT(window), "tooltip_data");
            if (old_data) g_free(old_data);
            g_object_set_data(G_OBJECT(window), "tooltip_data", NULL);
            g_source_remove(tooltip_timer);
            tooltip_timer = 0;
            gtk_tooltips_set_tip(
                    GTK_TOOLTIPS(tooltips),
                    textview,
                    "", "");
        }
    }
}

static gboolean
textview_event_after(GtkWidget* textview, GdkEvent* ev) {
    GtkWidget* window;
    GtkTextIter start, end, iter;
    GtkTextBuffer* buffer;
    GdkEventButton* event;
    GSList* tags = NULL;
    gint x, y;
    int len, n;

    if (is_processing) return FALSE;

    if (ev->type != GDK_BUTTON_RELEASE) return FALSE;
    event = (GdkEventButton*) ev;
    if (event->button != 1) return FALSE;

    window = gtk_widget_get_toplevel(textview);

    buffer = gtk_text_view_get_buffer(GTK_TEXT_VIEW(textview));
    gtk_text_buffer_get_selection_bounds(buffer, &start, &end);
    if (gtk_text_iter_get_offset(&start) != gtk_text_iter_get_offset(&end)) {
        return FALSE;
    }
    gtk_text_view_window_to_buffer_coords(
            GTK_TEXT_VIEW(textview),
            GTK_TEXT_WINDOW_WIDGET,
            (gint) event->x, (gint) event->y, &x, &y);
    gtk_text_view_get_iter_at_location(GTK_TEXT_VIEW(textview), &iter, x, y);

    tags = gtk_text_iter_get_tags(&iter);
    if (tags) {
        len = g_slist_length(tags);
        for(n = 0; n < len; n++) {
            GtkTextTag* tag = (GtkTextTag*) g_slist_nth_data(tags, n);
            if (tag) {
                gpointer tag_data;
                tag_data = g_object_get_data(G_OBJECT(tag), "url");
                if (tag_data) {
                    open_url((gchar*) tag_data);
                    break;
                }

                tag_data = g_object_get_data(G_OBJECT(tag), "user_id");
                if (tag_data) {
                    gchar* user_id = g_strdup(tag_data);
                    gchar* user_name = g_strdup(g_object_get_data(G_OBJECT(tag), "user_name"));
                    clean_context(window);
                    g_object_set_data(G_OBJECT(window), "user_id", user_id);
                    g_object_set_data(G_OBJECT(window), "user_name", user_name);
                    update_timeline(window, NULL);
                    break;
                }

                tag_data = g_object_get_data(G_OBJECT(tag), "status_url");
                if (tag_data) {
                    open_url((gchar*) tag_data);
                    break;
                }

                tag_data = g_object_get_data(G_OBJECT(tag), "retweet");
                if (tag_data) {
                    clean_context(window);
                    retweet_status(window, tag);
                    break;
                }

                tag_data = g_object_get_data(G_OBJECT(tag), "favorite");
                if (tag_data) {
                    favorite_status(window, tag);
                    break;
                }

                tag_data = g_object_get_data(G_OBJECT(tag), "reply");
                if (tag_data) {
                    gchar* text = NULL;
                    GtkWidget* entry;
                    gchar* in_reply_to_status_id = g_object_get_data(G_OBJECT(tag), "in_reply_to_status_id");

                    if (in_reply_to_status_id) {
                        in_reply_to_status_id = g_strdup(in_reply_to_status_id);
                        text = g_object_get_data(G_OBJECT(window), "in_reply_to_status_id");
                        if (text) g_free(text);
                        g_object_set_data(G_OBJECT(window), "in_reply_to_status_id", g_strdup(in_reply_to_status_id));
                    }
                    entry = (GtkWidget*) g_object_get_data(G_OBJECT(window), "entry");
                    text = g_strdup_printf("@%s ", (gchar*) tag_data);
                    gtk_entry_set_text(GTK_ENTRY(entry), text);
                    g_free(text);
                    gtk_widget_grab_focus(entry);
                    gtk_editable_set_position(GTK_EDITABLE(entry), -1);
                    break;
                }

                tag_data = g_object_get_data(G_OBJECT(tag), "tag_name");
                if (tag_data) {
                    gchar* word = g_strdup(tag_data);
                    clean_condition();
                    clean_context(window);
                    g_object_set_data(G_OBJECT(window), "mode", g_strdup("search"));
                    g_object_set_data(G_OBJECT(window), "search", word);
                    search_timeline(window, NULL);
                    break;
                }

            }
        }
        g_slist_free(tags);
    }
    return FALSE;
}

static gboolean
textview_motion(GtkWidget* textview, GdkEventMotion* event) {
    gint x, y;
    x = y = 0;
    gtk_text_view_window_to_buffer_coords(
            GTK_TEXT_VIEW(textview),
            GTK_TEXT_WINDOW_WIDGET,
            (gint) event->x, (gint) event->y, &x, &y);
    textview_change_cursor(textview, x, y);
    gdk_window_get_pointer(textview->window, NULL, NULL, NULL);
    return FALSE;
}

static gboolean
textview_visibility(GtkWidget* textview, GdkEventVisibility* event) {
    gint wx, wy, x, y;
    wx = wy = x = y = 0;
    gdk_window_get_pointer(textview->window, &wx, &wy, NULL);
    gtk_text_view_window_to_buffer_coords(
            GTK_TEXT_VIEW(textview),
            GTK_TEXT_WINDOW_WIDGET,
            wx, wy, &x, &y);
    textview_change_cursor(textview, x, y);
    gdk_window_get_pointer(textview->window, NULL, NULL, NULL);
    return FALSE;
}

static void
buffer_delete_range(GtkTextBuffer* buffer, GtkTextIter* start, GtkTextIter* end, gpointer user_data) {
    GtkTextIter* iter = gtk_text_iter_copy(end);
    const char* tag_names[] = {
        "url", "user_id", "user_name",
        "status_url", "retweet", "reply", "favorite", "in_reply_to_status_id",
        NULL
    };
    while(iter) {
        GSList* tags = NULL;
        int len, n;
        if (!gtk_text_iter_backward_char(iter)) break;
        if (!gtk_text_iter_in_range(iter, start, end)) break;
        tags = gtk_text_iter_get_tags(iter);
        if (!tags) continue;
        len = g_slist_length(tags);
        for(n = 0; n < len; n++) {
            const char** tag_name;
            gpointer tag_data;
            GtkTextTag* tag = (GtkTextTag*) g_slist_nth_data(tags, n);

            tag_name = tag_names;
            while (*tag_name) {
                tag_data = g_object_get_data(G_OBJECT(tag), *tag_name);
                if (tag_data) {
                    g_free(tag_data);
                    g_object_set_data(G_OBJECT(tag), *tag_name, NULL);
                }
                tag_name++;
            }
        }
        g_slist_free(tags);
    }
    gtk_text_iter_free(iter);
}

static void
swin_vadjust_value_changed(GtkAdjustment* vadjust, gpointer user_data) {
    GtkWidget* window = (GtkWidget*) user_data;
    if (!is_processing && gtk_adjustment_get_upper(vadjust) ==
        gtk_adjustment_get_value(vadjust)
        + gtk_adjustment_get_page_size(vadjust)) {

        gchar* mode = g_object_get_data(G_OBJECT(window), "mode");
        if (mode && (!strcmp(mode, "replies") || !strcmp(mode, "search"))) {
            gchar* page = g_object_get_data(G_OBJECT(window), "page");
            int page_no = atoi(page ? page : "1");
            if (page) g_free(page);
            g_object_set_data(G_OBJECT(window), "page", g_strdup_printf("%d", page_no+1));
        }
        clean_condition();
        if (mode && !strcmp(mode, "search")) {
            search_timeline(window, NULL);
        } else {
            update_timeline(window, NULL);
        }
    } else {
        reset_reload_timer(window);
    }
}

static void
config_dialog(GtkWidget* widget, gpointer user_data) {
    GtkWidget* window = (GtkWidget*) user_data;
    setup_dialog(window);
}

/**
 * configuration
 */
static int
load_config() {
    const gchar* confdir = g_get_user_config_dir();
    gchar* conffile = g_build_filename(confdir, APP_NAME, "config", NULL);
    char buf[BUFSIZ];
    FILE* fp = fopen(conffile, "rb");
    g_free(conffile);
    if (!fp) return -1;
    memset(&application_info, 0, sizeof(application_info));
    while(fgets(buf, sizeof(buf), fp)) {
        gchar* line = g_strchomp(buf);
        if (!strncmp(line, "consumer_key=", 13))
            application_info.consumer_key = strdup(line+13);
        if (!strncmp(line, "consumer_secret=", 16))
            application_info.consumer_secret = strdup(line+16);
        if (!strncmp(line, "access_token=", 13))
            application_info.access_token = strdup(line+13);
        if (!strncmp(line, "access_token_secret=", 20))
            application_info.access_token_secret = strdup(line+20);
        if (!strncmp(line, "font=", 5))
            application_info.font = strdup(line+5);
    }
    fclose(fp);
    return 0;
}

static int
save_config() {
    gchar* confdir = (gchar*) g_get_user_config_dir();
    gchar* conffile = NULL;
    FILE* fp = NULL;
    confdir = g_build_path(G_DIR_SEPARATOR_S, confdir, APP_NAME, NULL);
    g_mkdir_with_parents(confdir, 0700);
    conffile = g_build_filename(confdir, "config", NULL);
    g_free(confdir);
    fp = fopen(conffile, "wb");
    g_free(conffile);
    if (!fp) return -1;
#define SAFE_STRING(x) (x?x:"")
    fprintf(fp, "consumer_key=%s\n", SAFE_STRING(application_info.consumer_key));
    fprintf(fp, "consumer_secret=%s\n", SAFE_STRING(application_info.consumer_secret));
    fprintf(fp, "access_token=%s\n", SAFE_STRING(application_info.access_token));
    fprintf(fp, "access_token_secret=%s\n", SAFE_STRING(application_info.access_token_secret));
    fprintf(fp, "font=%s\n", SAFE_STRING(application_info.font));
#undef SAFE_STRING
    fclose(fp);
    return 0;
}

/**
 * main entry
 */
int
main(int argc, char* argv[]) {
    /* widgets */
    GtkWidget* window = NULL;
    GtkWidget* mainbox = NULL;
    GtkWidget* vbox = NULL;
    GtkWidget* hbox = NULL;
    GtkWidget* toolbox = NULL;
    GtkWidget* swin = NULL;
    GtkWidget* textview = NULL;
    GtkWidget* image = NULL;
    GtkWidget* button = NULL;
    GtkWidget* entry = NULL;
    GtkWidget* statusbar = NULL;
    GtkTooltips* tooltips = NULL;
    GtkWidget* loading_image = NULL;
    GtkWidget* loading_label = NULL;
    GtkAdjustment* vadjust = NULL;
    GtkAccelGroup* accelgroup = NULL;
    GtkTextBuffer* buffer = NULL;
    guint context_id;

    srandom(time(0));

#ifdef _LIBINTL_H
    setlocale(LC_CTYPE, "");

#ifdef LOCALE_SISO639LANGNAME
    if (getenv("LANG") == NULL) {
        char lang[256] = {0};
        if (GetLocaleInfo(LOCALE_USER_DEFAULT, LOCALE_SISO639LANGNAME, lang, sizeof(lang))) {
            char env[256] = {0};
            snprintf(env, sizeof(env)-1, "LANG=%s", lang);
            putenv(env);
        }
    }
#endif

    bindtextdomain(APP_NAME, LOCALE_DIR);
    bind_textdomain_codeset(APP_NAME, "utf-8");
    textdomain(APP_NAME);
#endif

    g_thread_init(NULL);
    gdk_threads_init();
    gdk_threads_enter();

    gtk_init(&argc, &argv);

    /*------------------*/
    /* building window. */

    /* main window */
    window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_title(GTK_WINDOW(window), APP_TITLE);
    g_signal_connect(G_OBJECT(window), "delete-event", gtk_main_quit, window);
    gtk_window_set_icon_from_file(GTK_WINDOW(window), DATA_DIR"/logo.png", NULL);

    /* accel group */
    accelgroup = gtk_accel_group_new();
    gtk_window_add_accel_group(GTK_WINDOW(window), accelgroup);

    /* link cursor */
    hand_cursor = gdk_cursor_new(GDK_HAND2);
    regular_cursor = gdk_cursor_new(GDK_XTERM);
    watch_cursor = gdk_cursor_new(GDK_WATCH);

    /* tooltips */
    tooltips = gtk_tooltips_new();
    g_object_set_data(G_OBJECT(window), "tooltips", tooltips);

    /* main box */
    mainbox = gtk_vbox_new(FALSE, 6);
    gtk_container_add(GTK_CONTAINER(window), mainbox);

    /* virtical container box */
    vbox = gtk_vbox_new(FALSE, 6);
    gtk_container_set_border_width(GTK_CONTAINER(vbox), 10);
    gtk_container_add(GTK_CONTAINER(mainbox), vbox);

    /* title logo */
    image = gtk_image_new_from_pixbuf(gdk_pixbuf_new_from_file(DATA_DIR"/twitter.png", NULL));
    gtk_box_pack_start(GTK_BOX(vbox), image, FALSE, TRUE, 0);

    /* status viewer on scrolled window */
    textview = gtk_text_view_new();
    gtk_text_view_set_editable(GTK_TEXT_VIEW(textview), FALSE);
    gtk_text_view_set_cursor_visible(GTK_TEXT_VIEW(textview), FALSE);
    gtk_text_view_set_wrap_mode(GTK_TEXT_VIEW(textview), GTK_WRAP_CHAR);
    g_signal_connect(textview, "motion-notify-event", G_CALLBACK(textview_motion), NULL);
    g_signal_connect(textview, "visibility-notify-event", G_CALLBACK(textview_visibility), NULL);
    g_signal_connect(textview, "event-after", G_CALLBACK(textview_event_after), NULL);
    g_object_set_data(G_OBJECT(window), "textview", textview);

    swin = gtk_scrolled_window_new(NULL, NULL);
    gtk_scrolled_window_set_policy(
            GTK_SCROLLED_WINDOW(swin),
            GTK_POLICY_NEVER,
            GTK_POLICY_AUTOMATIC);
    gtk_scrolled_window_add_with_viewport(GTK_SCROLLED_WINDOW(swin), textview);
    gtk_container_add(GTK_CONTAINER(vbox), swin);
    vadjust = gtk_scrolled_window_get_vadjustment(GTK_SCROLLED_WINDOW(swin));
    g_signal_connect(vadjust, "value-changed", G_CALLBACK(swin_vadjust_value_changed), window);

    buffer = gtk_text_view_get_buffer(GTK_TEXT_VIEW(textview));
    g_signal_connect(G_OBJECT(buffer), "delete-range", G_CALLBACK(buffer_delete_range), NULL);
    g_object_set_data(G_OBJECT(window), "buffer", buffer);

    /* toolbox */
    toolbox = gtk_vbox_new(FALSE, 6);
    gtk_box_pack_start(GTK_BOX(vbox), toolbox, FALSE, TRUE, 0);
    g_object_set_data(G_OBJECT(window), "toolbox", toolbox);

    /*--------------------------------------*/
    /* horizontal container box for buttons */
    hbox = gtk_hbox_new(FALSE, 6);
    gtk_box_pack_start(GTK_BOX(toolbox), hbox, FALSE, TRUE, 0);

    /* home button */
    button = gtk_button_new();
    g_signal_connect(G_OBJECT(button), "clicked", G_CALLBACK(home_timeline), window);
    image = gtk_image_new_from_pixbuf(gdk_pixbuf_new_from_file(DATA_DIR"/home.png", NULL));
    gtk_container_add(GTK_CONTAINER(button), image);
    gtk_box_pack_start(GTK_BOX(hbox), button, FALSE, TRUE, 0);
    gtk_tooltips_set_tip(
            GTK_TOOLTIPS(tooltips),
            button,
            _("go home"),
            _("go home"));
    gtk_widget_add_accelerator(button, "activate", accelgroup, GDK_h, GDK_CONTROL_MASK, GTK_ACCEL_VISIBLE); 

    /* replies button */
    button = gtk_button_new();
    g_signal_connect(G_OBJECT(button), "clicked", G_CALLBACK(replies_timeline), window);
    image = gtk_image_new_from_pixbuf(gdk_pixbuf_new_from_file(DATA_DIR"/replies.png", NULL));
    gtk_container_add(GTK_CONTAINER(button), image);
    gtk_box_pack_start(GTK_BOX(hbox), button, FALSE, TRUE, 0);
    gtk_tooltips_set_tip(
            GTK_TOOLTIPS(tooltips),
            button,
            _("replies"),
            _("replies"));
    gtk_widget_add_accelerator(button, "activate", accelgroup, GDK_r, GDK_CONTROL_MASK, GTK_ACCEL_VISIBLE); 

    /* reload button */
    button = gtk_button_new();
    g_signal_connect(G_OBJECT(button), "clicked", G_CALLBACK(on_reload_clicked), window);
    image = gtk_image_new_from_pixbuf(gdk_pixbuf_new_from_file(DATA_DIR"/reload.png", NULL));
    gtk_container_add(GTK_CONTAINER(button), image);
    gtk_box_pack_start(GTK_BOX(hbox), button, FALSE, TRUE, 0);
    gtk_tooltips_set_tip(
            GTK_TOOLTIPS(tooltips),
            button,
            _("reload statuses"),
            _("reload statuses"));
    gtk_widget_add_accelerator(button, "activate", accelgroup, GDK_g, GDK_CONTROL_MASK, GTK_ACCEL_VISIBLE); 

    /* search button */
    button = gtk_button_new();
    g_signal_connect(G_OBJECT(button), "clicked", G_CALLBACK(search_dialog), window);
    image = gtk_image_new_from_pixbuf(gdk_pixbuf_new_from_file(DATA_DIR"/search.png", NULL));
    gtk_container_add(GTK_CONTAINER(button), image);
    gtk_box_pack_start(GTK_BOX(hbox), button, FALSE, TRUE, 0);
    gtk_tooltips_set_tip(
            GTK_TOOLTIPS(tooltips),
            button,
            _("search word"),
            _("search word"));
    gtk_widget_add_accelerator(button, "activate", accelgroup, GDK_f, GDK_CONTROL_MASK, GTK_ACCEL_VISIBLE); 

    /* config button */
    button = gtk_button_new();
    g_signal_connect(G_OBJECT(button), "clicked", G_CALLBACK(config_dialog), window);
    image = gtk_image_new_from_pixbuf(gdk_pixbuf_new_from_file(DATA_DIR"/config.png", NULL));
    gtk_container_add(GTK_CONTAINER(button), image);
    gtk_box_pack_start(GTK_BOX(hbox), button, FALSE, TRUE, 0);
    gtk_tooltips_set_tip(
            GTK_TOOLTIPS(tooltips),
            button,
            _("show config dialog"),
            _("show config dialog"));

    /* loading animation */
    loading_image = gtk_image_new_from_file(DATA_DIR"/loading.gif");
    if (loading_image) {
        gtk_box_pack_start(GTK_BOX(hbox), loading_image, FALSE, TRUE, 0);
        g_object_set_data(G_OBJECT(window), "loading-image", loading_image);
    }

    loading_label = gtk_label_new("");
    gtk_box_pack_start(GTK_BOX(hbox), loading_label, FALSE, TRUE, 0);
    g_object_set_data(G_OBJECT(window), "loading-label", loading_label);

    /*----------------------------------------------------*/
    /* horizontal container box for entry and post button */
    hbox = gtk_hbox_new(FALSE, 6);
    gtk_box_pack_start(GTK_BOX(toolbox), hbox, FALSE, TRUE, 0);

    /* text entry */
    entry = gtk_entry_new();
    g_object_set_data(G_OBJECT(window), "entry", entry);
    g_signal_connect(G_OBJECT(entry), "activate", G_CALLBACK(on_entry_activate), window);
    gtk_entry_set_max_length(GTK_ENTRY(entry), 140);
    gtk_box_pack_start(GTK_BOX(hbox), entry, TRUE, TRUE, 0);
    /* gtk_widget_set_size_request(entry, -1, 50); */
    gtk_tooltips_set_tip(
            GTK_TOOLTIPS(tooltips),
            entry,
            _("what are you doing?"),
            _("what are you doing?"));
    g_object_set(gtk_widget_get_settings(entry), "gtk-entry-select-on-focus", FALSE, NULL);
    gtk_widget_add_accelerator(entry, "grab-focus", accelgroup, GDK_l, GDK_CONTROL_MASK, GTK_ACCEL_VISIBLE); 

    /* post button */
    button = gtk_button_new();
    g_signal_connect(G_OBJECT(button), "clicked", G_CALLBACK(post_status), window);
    image = gtk_image_new_from_pixbuf(gdk_pixbuf_new_from_file(DATA_DIR"/post.png", NULL));
    gtk_container_add(GTK_CONTAINER(button), image);
    gtk_box_pack_start(GTK_BOX(hbox), button, FALSE, TRUE, 0);
    gtk_tooltips_set_tip(
            GTK_TOOLTIPS(tooltips),
            button,
            _("post status"),
            _("post status"));

    /* status bar */
    statusbar = gtk_statusbar_new();
    g_object_set_data(G_OBJECT(window), "statusbar", statusbar);
    gtk_box_pack_end(GTK_BOX(mainbox), statusbar, FALSE, TRUE, 0);
    context_id = gtk_statusbar_get_context_id(GTK_STATUSBAR (statusbar), "API status");
    g_object_set_data(G_OBJECT(statusbar), "context_id", (gpointer) context_id);
    gtk_statusbar_push(GTK_STATUSBAR(statusbar), context_id, "");

    /* request initial window size */
    gtk_widget_set_size_request(window, 300, 400);
    gtk_widget_show_all(mainbox);
    gtk_widget_show(window);

    if (loading_image) gtk_widget_hide(loading_image);
    gtk_widget_hide(loading_label);

    /* default consumer info */
    memset(&application_info, 0, sizeof(application_info));

    application_info.consumer_key = strdup("CONSUMER_KEY");
    application_info.consumer_secret = strdup("CONSUMER_SECRET");

    load_config();

    if (application_info.font && strlen(application_info.font)) {
        PangoFontDescription* pangoFont = NULL;
        pangoFont = pango_font_description_new();
        pango_font_description_set_family(pangoFont, application_info.font);
        gtk_widget_modify_font(textview, pangoFont);
        pango_font_description_free(pangoFont);
    }

    check_ratelimit(window, statusbar);

    update_timeline(window, NULL);

    gtk_main();

    gdk_threads_leave();

    return 0;
}

#ifdef _WIN32
int WINAPI WinMain(
        HINSTANCE hCurInst, HINSTANCE hPrevInst,
        LPSTR lpsCmdLine, int nCmdShow) {
    return main(__argc, __argv);
}
#endif

/* vim:set et sw=4: */
