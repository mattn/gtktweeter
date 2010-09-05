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
#include <curl/curl.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

/**
 * for xauth
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
        sha1_context *ctx)
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
        sha1_context *ctx, const unsigned char data[64])
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
        sha1_context *ctx,
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
        memcpy((void*)(ctx->buffer + left), (void*)input, fill);
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
        memcpy((void*)(ctx->buffer + left), (void *)input, length );
}

static unsigned char sha1_padding[64] =
{
    0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};

static void sha1_finish(
        sha1_context *ctx,
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
        temp[j++] = hex_table[((unsigned char)input[i] & 0xF0) >> 4];
        temp[j++] = hex_table[(unsigned char)input[i]& 0x0F];
    }
    return temp;
}

static const char* base64chars = 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz"
    "0123456789+/";
#define is_base64(c) ( \
        isalnum((unsigned char)c) || \
        ((unsigned char)c == '+') || \
        ((unsigned char)c == '/'))

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
    char* temp = (char*) calloc(len * 2 + 1, sizeof(char));
    char* ret = temp;
    for (i = 0; i < len; i++) {
        unsigned char c = (unsigned char)url[i];
        if (isalnum(c) || c == '_' || c == '.' || c == '-')
            *temp++ = c;
        else {
            char buf[8];
            sprintf(buf, "%02x", c);
            *temp++ = '%';
            *temp++ = buf[0];
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
    unsigned char ipad[65];
    unsigned char opad[65];
    unsigned char inner[21];
    
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

typedef struct {
    char* data;     // response data from server
    size_t size;    // response size of data
} MEMFILE;

MEMFILE*
memfopen() {
    MEMFILE* mf = (MEMFILE*) malloc(sizeof(MEMFILE));
    mf->data = NULL;
    mf->size = 0;
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
    char* buf = (char*) malloc(mf->size + 1);
    memcpy(buf, mf->data, mf->size);
    buf[mf->size] = 0;
    return buf;
}

int main(int argc, char* argv[])
{
    char key[4096];
    char query[4096];
    char text[4096];
    char auth[21];
    char tmstr[10];
    char nonce[21];
    char error[CURL_ERROR_SIZE];
    const char* access_url = "https://api.twitter.com/oauth/access_token";
    const char* post_url = "http://twitter.com/statuses/update.json";
    char* consumer_key = "knvZzOc7BH9dDPFgTJJsng";
    char* consumer_secret = "Npa03C4TfaI1YcZ4So0dSO4qeNigAsupPq7PGPM";
    char* username;
    char* password;
    char* message;
    char* oauth_token = NULL;
    char* oauth_token_secret = NULL;
    CURL* curl = NULL;
    CURLcode res = CURLE_OK;
    struct curl_slist *headers = NULL;
    char* tmp;
    char* ptr;
    char* stop;
    MEMFILE* mf; // mem file

    if (argc != 4) {
        fprintf(stderr, "usage: %s [username] [password] [message]\n", argv[0]);
        exit(-1);
    }

    username = argv[1];
    password = argv[2];
    message = argv[3];

    curl = curl_easy_init();

    sprintf(tmstr, "%08d", (int) time(0));
    ptr = to_hex_alloc(tmstr);
    strcpy(nonce, ptr);
    free(ptr);

    sprintf(query,
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%s"
        "&oauth_version=1.0"
        "&x_auth_mode=client_auth"
        "&x_auth_password=%s"
        "&x_auth_username=%s",
            consumer_key,
            nonce,
            tmstr,
            password,
            username);

    strcpy(text, "POST&");
    ptr = urlencode_alloc(access_url);
    strcat(text, ptr);
    free(ptr);
    strcat(text, "&");
    ptr = urlencode_alloc(query);
    strcat(text, ptr);
    free(ptr);

    sprintf(key, "%s&", consumer_secret);
    hmac((unsigned char*)key, strlen(key),
            (unsigned char*)text, strlen(text), (unsigned char*) auth);
    strcat(query, "&oauth_signature=");
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    strcat(query, ptr);
    free(tmp);
    free(ptr);
    printf("%s\n", query);

    mf = memfopen();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, access_url);
    curl_easy_setopt(curl, CURLOPT_POST, 1);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, query);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mf);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    if (res != CURLE_OK) {
        fputs(error, stderr);
        memfclose(mf);
        goto leave;
    }
    ptr = memfstrdup(mf);
    printf("%s\n", ptr);
    if (1) goto leave;
    memfclose(mf);
    tmp = strstr(ptr, "oauth_token=");
    if (tmp) {
        stop = strchr(tmp, '&');
        if (stop) {
            oauth_token = (char*) calloc(stop - tmp - 11, sizeof(char));
            strncpy(oauth_token, tmp + 12, stop - tmp - 12);
        } else
            oauth_token = strdup(tmp + 12);
    } else {
        fputs(ptr, stderr);
        goto leave;
    }
    tmp = strstr(ptr, "oauth_token_secret=");
    if (tmp) {
        stop = strchr(tmp, '&');
        if (stop) {
            oauth_token_secret = (char*) calloc(stop - tmp - 18, sizeof(char));
            strncpy(oauth_token_secret, tmp + 19, stop - tmp - 19);
        } else
            oauth_token = strdup(tmp + 19);
    }
    //printf("oauth_token=%s\n", oauth_token);
    //printf("oauth_token_secret=%s\n", oauth_token_secret);
    free(ptr);

    sprintf(tmstr, "%08d", (int) time(0));
    ptr = to_hex_alloc(tmstr);
    strcpy(nonce, ptr);
    free(ptr);

    sprintf(key, "%s&%s", consumer_secret, oauth_token_secret);
    tmp = urlencode_alloc(message);
    sprintf(query,
        "oauth_consumer_key=%s"
        "&oauth_nonce=%s"
        "&oauth_signature_method=HMAC-SHA1"
        "&oauth_timestamp=%s"
        "&oauth_token=%s"
        "&oauth_version=1.0"
        "&status=%s",
            consumer_key,
            nonce,
            tmstr,
            oauth_token,
            tmp);
    free(tmp);

    strcpy(text, "POST&");
    ptr = urlencode_alloc(post_url);
    strcat(text, ptr);
    free(ptr);
    strcat(text, "&");
    ptr = urlencode_alloc(query);
    strcat(text, ptr);
    free(ptr);

    hmac((unsigned char*)key, strlen(key),
            (unsigned char*)text, strlen(text), (unsigned char*) auth);
    stop = strstr(query, "&status=");
    if (stop) *stop = 0;
    strcat(query, "&oauth_signature=");
    tmp = base64encode_alloc(auth, 20);
    ptr = urlencode_alloc(tmp);
    strcat(query, ptr);
    free(tmp);
    free(ptr);

    ptr = query;
    while (*ptr) {
        if (*ptr == '&') *ptr = ',';
        ptr++;
    }
    sprintf(text, "Authorization: OAuth %s", query);
    headers = curl_slist_append(headers, text);

    ptr = urlencode_alloc(message);
    sprintf(text, "status=%s", ptr);
    free(ptr);

    mf = memfopen();
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 0);
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, error);
    curl_easy_setopt(curl, CURLOPT_URL, post_url);
    curl_easy_setopt(curl, CURLOPT_POST, 1);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, text);
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, memfwrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, mf);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1);
    res = curl_easy_perform(curl);
    curl_slist_free_all(headers);
    if (res != CURLE_OK) {
        fputs(error, stderr);
        memfclose(mf);
        goto leave;
    }
    ptr = memfstrdup(mf);
    memfclose(mf);
    free(ptr);

leave:
    curl_easy_cleanup(curl);
    return 0;
}

/* vim:set et sw=4: */
