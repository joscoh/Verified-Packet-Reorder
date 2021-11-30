/*
 *
 * Copyright (c) 2007-2020 The University of Waikato, Hamilton, New Zealand.
 * All rights reserved.
 *
 * This file is part of libtrace.
 *
 * This code has been developed by the University of Waikato WAND
 * research group. For further information please see http://www.wand.net.nz/
 *
 * libtrace is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * libtrace is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 */

// We only copy the parts that we need, so that Verifast does not complain about the rest

#ifndef LIBTRACE_H
#define LIBTRACE_H

/** @file
 *
 * @brief Trace file processing library header
 *
 * @author Daniel Lawson
 * @author Perry Lorier
 * @author Shane Alcock
 * @author Richard Sanger
 *
 * This library provides a per packet interface into a trace file, or a live
 * captures.  It supports ERF, DAG cards, PCAP, Linux and BSD native sockets,
 * legacy ERF formats etc.
 *
 * @par Usage
 * See the example/ directory in the source distribution for some simple
 * examples
 *
 * @par Linking
 * To use this library you need to link against libtrace by passing -ltrace
 * to your linker.
 *
 * See libtrace_parallel.h for a description of the parallel API that allows
 * programmers to spread packet processing across multiple threads.
 *
 */

#include <sys/types.h>
#include <stddef.h>
#include <stdio.h>
/* Compile time assertion. Sourced from:
 * http://www.pixelbeat.org/programming/gcc/static_assert.html */
#define ct_assert(e) extern char (*ct_assert(void)) [sizeof(char[1 - 2*!(e)])]

#ifndef WIN32
#include <sys/time.h>
#endif

#if ENABLE_DTRACE
#include <sys/sdt.h>
#endif

/* Deal with missing byte order macros */
#include <sys/param.h>

#if defined(BYTE_ORDER) && !defined(__BYTE_ORDER)
#define __BYTE_ORDER 	BYTE_ORDER
#endif

#if defined(BIG_ENDIAN) && !defined(__BIG_ENDIAN)
#define __BIG_ENDIAN	BIG_ENDIAN
#endif

#if defined(LITTLE_ENDIAN) && !defined(__LITTLE_ENDIAN)
#define __LITTLE_ENDIAN	LITTLE_ENDIAN
#endif

#ifdef WIN32
#   include <winsock2.h>
#   include <ws2tcpip.h>
    typedef short sa_family_t;
    /* Make up for a lack of stdbool.h */
#    define bool signed char
#    define false 0
#    define true 1
#    if !defined(ssize_t)
     /* XXX: Not 64-bit safe! */
#    define ssize_t int
#    endif    
#else
#    include <netinet/in.h>

#ifndef __cplusplus
#    include <stdbool.h>
#endif

#    include <sys/types.h>
#    include <sys/socket.h>
#endif

/** API version as 2 byte hex digits, eg 0xXXYYZZ */
#define LIBTRACE_API_VERSION \
            ((4<<16)|(0<<8)|(17))

/** This used to be replaced with the current SVN revision number when 
 * 'make dist' was invoked to create a distributable tarball. We don't use
 * SVN anymore and there probably isn't any need to know the exact revision
 * number either these days. */
#define LIBTRACE_SVN_REVISION LIBTRACE_API_VERSION

/** DAG driver version installed on the current system */
#define DAG_DRIVER_V ""

/**
  * A version of assert that always runs the first argument even
  * when not debugging, however only asserts the condition if debugging
  * Intended for use mainly with pthread locks etc. which have error
  * returns but *should* never actually fail.
  */
#ifdef NDEBUG
#define ASSERT_RET(run, cond) run
#else
#define ASSERT_RET(run, cond) assert(run cond)
//#define ASSERT_RET(run, cond) run
#endif
    
#ifdef __cplusplus 
extern "C" { 
#endif

#ifdef _MSC_VER
    /* define the following from MSVC's internal types */
    typedef             __int8  int8_t;
    typedef             __int16 int16_t;
    typedef             __int32 int32_t;
    typedef             __int64 int64_t;
    typedef unsigned    __int8  uint8_t;
    typedef unsigned    __int16 uint16_t;
    typedef unsigned    __int32 uint32_t;
    typedef unsigned    __int64 uint64_t;
    
    /* Windows pads bitfields out to to the size of their parent type
     * however gcc warns that this doesn't meet with the iso C specification
     * so produces warnings for this behaviour.  sigh.
     */
    #define LT_BITFIELD8        uint8_t
    #define LT_BITFIELD16       uint16_t
    #define LT_BITFIELD32       uint32_t
    #define LT_BITFIELD64       uint64_t
#else
    #ifdef HAVE_STDINT_H
        #   include <stdint.h>
    #endif
    /* GCC warns if the bitfield type is not "unsigned int", however windows
     * generates incorrect code for this (see above), so we define these
     * macros.  How Hideous.  So much for C's portability.
     */
    #define LT_BITFIELD8        unsigned int
    #define LT_BITFIELD16       unsigned int
    #define LT_BITFIELD32       unsigned int
    #define LT_BITFIELD64       unsigned int
#endif

/* Ensure these gcc optimisation attributes are defined consistently, 
 * without requiring users to need to have access to the config.h 
 * generated by running configure.
 */

#define LT_USE_PACKED 1
#define LT_USE_ALIGNED 1
#define LT_USE_UNUSED 1
#define LT_USE_DEPRECATED 1
#define LT_USE_PURE 0
#define LT_USE_PRINTF 1
#define LT_USE_VISIBILITY 1

#if LT_USE_PACKED
#  define PACKED __attribute__((packed))
#else
#  define PACKED
#endif

#if LT_USE_ALIGNED
# define ALIGNED(x) __attribute__((aligned(x)))
#else
# define ALIGNED(x)
#endif

#if LT_USE_UNUSED
#  define UNUSED __attribute__((unused))
#else
#  define UNUSED
#endif

#if LT_USE_DEPRECATED
#  define DEPRECATED __attribute__((deprecated))
#else
#  define DEPRECATED
#endif

#if LT_USE_PURE
#  define SIMPLE_FUNCTION __attribute__((pure))
#else
#  define SIMPLE_FUNCTION
#endif

#if LT_USE_PRINTF
#  define PRINTF(formatpos, argpos) __attribute__((format(printf,formatpos, argpos)))
#else
#  define PRINTF(formatpos, argpos)
#endif

#ifndef CACHE_LINE_SIZE
#define CACHE_LINE_SIZE 64
#endif

#ifdef _MSC_VER
    #ifdef LT_BUILDING_DLL
        #define DLLEXPORT __declspec(dllexport)
    #else
        #define DLLEXPORT __declspec(dllimport)
    #endif
    #define DLLLOCAL
#else
    #ifndef DLLEXPORT
        #if LT_USE_VISIBILITY && LT_BUILDING_DLL
            #define DLLEXPORT __attribute__ ((visibility("default")))
            #define DLLLOCAL __attribute__ ((visibility("hidden")))
        #else
            #define DLLEXPORT
            #define DLLLOCAL
        #endif
    #endif
#endif

typedef uint64_t lt_unaligned_uint64_t ALIGNED(1);
typedef uint32_t lt_unaligned_uint32_t ALIGNED(1);
typedef uint16_t lt_unaligned_uint16_t ALIGNED(1);
typedef uint8_t lt_unaligned_uint8_t ALIGNED(1);

typedef int64_t lt_unaligned_int64_t ALIGNED(1);
typedef int32_t lt_unaligned_int32_t ALIGNED(1);
typedef int16_t lt_unaligned_int16_t ALIGNED(1);
typedef int8_t lt_unaligned_int8_t ALIGNED(1);

#define LIBTRACE_MIN(a,b) ((a)<(b) ? (a) : (b))

/** Opaque structure holding information about an output trace */
typedef struct libtrace_out_t libtrace_out_t;

/** Opaque structure holding information about a trace */
typedef struct libtrace_t libtrace_t;

/** Opaque structure holding information about a bpf filter */
typedef struct libtrace_filter_t libtrace_filter_t;

/** Opaque structure holding information about libtrace thread */
typedef struct libtrace_thread_t libtrace_thread_t;

/** Opaque structure holding callback functions for libtrace threads */
typedef struct callback_set libtrace_callback_set_t;

/** If the packet has allocated its own memory the buffer_control should be
 * set to TRACE_CTRL_PACKET, so that the memory will be freed when the packet
 * is destroyed. If the packet has been zero-copied out of memory owned by
 * something else, e.g. a DAG card, it should be TRACE_CTRL_EXTERNAL.
 *
 * @note The letters p and e are magic numbers used to detect if the packet
 * wasn't created properly.
 */
typedef enum {
	TRACE_CTRL_PACKET='p',  /**< Buffer memory is owned by the packet */
	TRACE_CTRL_EXTERNAL='e' /**< Buffer memory is owned by an external source */
} buf_control_t;

/** The size of a packet's buffer when managed by libtrace */
#define LIBTRACE_PACKET_BUFSIZE 65536

/** Libtrace error information */
typedef struct trace_err_t{
	int err_num; 		/**< error code */
	char problem[1024];	/**< the format, uri etc that caused the error for reporting purposes */
} libtrace_err_t;

/** Enumeration of error codes */
enum {
	/** No Error has occurred.... yet. */
	TRACE_ERR_NOERROR 	= 0,
	/** The URI passed to trace_create() is unsupported, or badly formed */
	TRACE_ERR_BAD_FORMAT 	= -1,
	/** The trace failed to initialise */
	TRACE_ERR_INIT_FAILED 	= -2,
	/** Unknown config option */
	TRACE_ERR_UNKNOWN_OPTION= -3,
	/** This output uri cannot write packets of this type */
	TRACE_ERR_NO_CONVERSION = -4,
	/** This packet is corrupt, or unusable for the action required */ 
	TRACE_ERR_BAD_PACKET	= -5,
	/** Option known, but unsupported by this format */
	TRACE_ERR_OPTION_UNAVAIL= -6,
	/** This feature is unsupported */
	TRACE_ERR_UNSUPPORTED	= -7,
	/** Illegal use of the API */
	TRACE_ERR_BAD_STATE	= -8,
	/** Failed to compile a BPF filter */
	TRACE_ERR_BAD_FILTER    = -9,
	/** RT communication breakdown */
	TRACE_ERR_RT_FAILURE    = -10,
	/** Compression format unsupported */
	TRACE_ERR_UNSUPPORTED_COMPRESS 	= -11,
        /** Wandio has returned an error */
        TRACE_ERR_WANDIO_FAILED = -12,
	/** Input URI (file) not found */
        TRACE_ERR_URI_NOT_FOUND = -13,
	/** NULL passed to create trace **/
	TRACE_ERR_URI_NULL = -14,
	/** NULL trace passed to trace_start **/
	TRACE_ERR_NULL_TRACE = -15,
	/** Unable to finish last packet in trace_pause **/
	TRACE_ERR_PAUSE_FIN = -16,
	/** Packet is NULL **/
	TRACE_ERR_NULL_PACKET = -17,
	/** Filter is NULL **/
	TRACE_ERR_NULL_FILTER = -18,
	/** Buffer is NULL **/
	TRACE_ERR_NULL_BUFFER = -19,
	/** Trace stats err **/
	TRACE_ERR_STAT = -20,
	/** Unable to create deadtrace **/
	TRACE_ERR_CREATE_DEADTRACE = -21,
	/** Bad linktype **/
	TRACE_ERR_BAD_LINKTYPE = -22,
	/** Bad IO for the trace **/
	TRACE_ERR_BAD_IO = -23,
	/** Trace has bad header **/
	TRACE_ERR_BAD_HEADER = -24,
	/** Trace err seeking by erf **/
	TRACE_ERR_SEEK_ERF = -25,
	/** Trace err combiner **/
	TRACE_ERR_COMBINER = -26,
	/** Error pausing processing thread **/
	TRACE_ERR_PAUSE_PTHREAD = -27,
	/** Error with trace thread **/
	TRACE_ERR_THREAD = -28,
	/** Thread in unexpecting state **/
	TRACE_ERR_THREAD_STATE = -29,
	/** Trace configuration error **/
	TRACE_ERR_CONFIG = -30,
	/** NULL passed misc **/
	TRACE_ERR_NULL = -31,
	/** Err with trace output file **/
	TRACE_ERR_OUTPUT_FILE = -32,
	/** Err out of memory **/
	TRACE_ERR_OUT_OF_MEMORY = -33,
};

/** Enumeration of DLTs supported by libtrace 
 */
typedef enum {
	/* Special value used to indicate a failure to convert to libtrace
         * DLT */
        TRACE_DLT_ERROR = -1,

	/** pcap documents this as having the Address Family value in host 
          * byte order as the framing.  Ugly? Yes.
 	  */
	TRACE_DLT_NULL = 0, 
	TRACE_DLT_EN10MB = 1,
	TRACE_DLT_PPP = 9,
	TRACE_DLT_ATM_RFC1483 = 11,

	/** Ok, so OpenBSD has a different value for DLT_RAW as the rest of
         * the planet, so detect this.  When reading to/from files we should
         * be using TRACE_DLT_LINKTYPE_RAW instead. When talking about DLT's
         * inside libtrace tho, we should be using /these/ DLT's.
         */
#ifdef __OpenBSD__
	TRACE_DLT_OPENBSD_LOOP=12,
	TRACE_DLT_RAW = 14,
#else
	TRACE_DLT_RAW = 12,
	TRACE_DLT_OPENBSD_LOOP = 108,
#endif
	TRACE_DLT_PPP_SERIAL = 50,
	TRACE_DLT_LINKTYPE_RAW = 101, /**< See TRACE_DLT_RAW for explanations of pain. */
	TRACE_DLT_C_HDLC = 104,
	TRACE_DLT_IEEE802_11 = 105,
	TRACE_DLT_LINUX_SLL = 113,
	TRACE_DLT_PFLOG = 117,
	TRACE_DLT_IEEE802_11_RADIO = 127 /**< Radiotap */
} libtrace_dlt_t ;

/** Enumeration of link layer types supported by libtrace */
typedef enum {
       TRACE_TYPE_CONTENT_INVALID = -2, /**< Packet contents are not valid */
       TRACE_TYPE_UNKNOWN = -1,		/**< Unable to determine link type */
    /* TRACE_TYPE_LEGACY = 0 		Obsolete */
       TRACE_TYPE_HDLC_POS = 1, 	/**< HDLC over POS */
       TRACE_TYPE_ETH = 2,		/**< 802.3 style Ethernet */
       TRACE_TYPE_ATM = 3,		/**< ATM frame */
       TRACE_TYPE_80211 = 4,		/**< 802.11 frames */
       TRACE_TYPE_NONE = 5,		/**< Raw IP frames */
       TRACE_TYPE_LINUX_SLL = 6,	/**< Linux "null" framing */
       TRACE_TYPE_PFLOG = 7,		/**< FreeBSD's PFlog */
    /* TRACE_TYPE_LEGACY_DEFAULT	Obsolete */
       TRACE_TYPE_POS = 9,		/**< Packet-over-SONET */
    /* TRACE_TYPE_LEGACY_ATM 		Obsolete */
    /* TRACE_TYPE_LEGACY_ETH 		Obsolete */
       TRACE_TYPE_80211_PRISM = 12,	/**< 802.11 Prism frames */
       TRACE_TYPE_AAL5 = 13,		/**< ATM Adaptation Layer 5 frames */
       TRACE_TYPE_DUCK = 14,	     /**< Pseudo link layer for DUCK packets */
       TRACE_TYPE_80211_RADIO = 15,  /**< Radiotap + 802.11 */
       TRACE_TYPE_LLCSNAP = 16,      /**< Raw LLC/SNAP */
       TRACE_TYPE_PPP = 17,	     /**< PPP frames */
       TRACE_TYPE_METADATA = 18,     	/**< WDCAP-style meta-data */
       TRACE_TYPE_NONDATA = 19,		/**< Not a data packet */
       TRACE_TYPE_OPENBSD_LOOP = 20,	/**< OpenBSD loopback */
       TRACE_TYPE_ERF_META = 21, /**< ERF Provenance metadata record */
       TRACE_TYPE_ETSILI = 22,	/**< ETSI Lawful Intercept */
       TRACE_TYPE_PCAPNG_META = 23,	/** PCAPNG meta packet */
       TRACE_TYPE_TZSP = 24,		/** TZSP Live packets */
       TRACE_TYPE_CORSAROTAG = 25,      /** Corsaro tagged packets */
       TRACE_TYPE_XDP = 26,             /** AF_XDP */
} libtrace_linktype_t;

/** RT protocol base format identifiers.
 * This is used to describe the capture format of the packet is being sent 
 * using the RT protocol.
 */ 
enum base_format_t {
        TRACE_FORMAT_ERF          =1,	/**< ERF (DAG capture format) */
        TRACE_FORMAT_PCAP         =2,	/**< Live PCAP capture */
        TRACE_FORMAT_PCAPFILE     =3,	/**< PCAP trace file */ 
        TRACE_FORMAT_WAG          =4,	/**< WAG live capture (Obsolete) */
        TRACE_FORMAT_RT           =5,	/**< RT network protocol */
        TRACE_FORMAT_LEGACY_ATM   =6,	/**< Legacy ERF for ATM capture */
	TRACE_FORMAT_LEGACY_POS	  =7,	/**< Legacy ERF for POS capture */
	TRACE_FORMAT_LEGACY_ETH   =8,	/**< Legacy ERF for ETH capture */
	TRACE_FORMAT_LINUX_NATIVE =9,	/**< Linux native interface capture */
	TRACE_FORMAT_DUCK	  =10,	/**< DAG Clock information */
	TRACE_FORMAT_BPF	  =11,	/**< BSD native interface capture */
	TRACE_FORMAT_TSH	  =12,	/**< TSH trace format */
	TRACE_FORMAT_ATMHDR	  =13,	/**< Legacy ATM header capture */
	TRACE_FORMAT_LEGACY_NZIX  =14,	/**< Legacy format used for NZIX traces */
	TRACE_FORMAT_LINUX_RING	  =15,	/**< Linux native interface capture PACKET_MMAP */
	TRACE_FORMAT_RAWERF	  =16,	/**< Special format for reading uncompressed ERF traces without checking for compression */
        TRACE_FORMAT_DPDK     =17, /**< The Intel Data Plane Development Kit format */
        TRACE_FORMAT_PCAPNG     =18,    /**< PCAP-NG trace file */
        TRACE_FORMAT_NDAG       =19,    /**< DAG multicast over a network */
        TRACE_FORMAT_DPDK_NDAG       =20,    /**< DAG multicast over a network, received via DPDK */
        TRACE_FORMAT_ETSILIVE     =21,  /**< ETSI LI over a network */
	TRACE_FORMAT_UNKNOWN      =22,  /** Unknown format */
	TRACE_FORMAT_TZSPLIVE	  =23,  /** TZSP */
        TRACE_FORMAT_CORSAROTAG   =24,  /** Corsarotagger format */
        TRACE_FORMAT_XDP          =25,  /** AF_XDP format */
	TRACE_FORMAT_PFRINGOLD	  =26,
	TRACE_FORMAT_PFRING       =27,
};

/** RT protocol packet types */
typedef enum {
	TRACE_RT_HELLO       	=1, /**< Connection accepted */
	TRACE_RT_START		=2, /**< Request for data transmission to begin 
				    */
	TRACE_RT_ACK		=3, /**< Data acknowledgement */
	TRACE_RT_STATUS		=4, /**< Fifo status packet */
	TRACE_RT_DUCK		=5, /**< Dag duck info packet */
	TRACE_RT_END_DATA	=6, /**< Server is exiting message */
	TRACE_RT_CLOSE		=7, /**< Client is exiting message */
	TRACE_RT_DENY_CONN	=8, /**< Connection has been denied */
	TRACE_RT_PAUSE		=9, /**< Request server to suspend sending data 
				     */
	TRACE_RT_PAUSE_ACK	=10,/**< Server is paused message */
	TRACE_RT_OPTION	 	=11,/**< Option request */
	TRACE_RT_KEYCHANGE	=12,/**< Anonymisation key has changed */ 
	TRACE_RT_DUCK_2_4	=13,/**< Dag 2.4 Duck */
	TRACE_RT_DUCK_2_5 	=14,/**< Dag 2.5 Duck */
	TRACE_RT_LOSTCONN 	=15,/**< Lost connection to server */
	TRACE_RT_SERVERSTART	=16,/**< Reliable server has been restarted */
	TRACE_RT_CLIENTDROP	=17,/**< Reliable client was lost */
	TRACE_RT_METADATA	=18,/**< Packet contains server meta-data */
	TRACE_RT_DUCK_5_0 	=19,/**< Dag 5.0 Duck */
        TRACE_RT_PCAPNG_META    =20,/**< Metadata for a PCAP NG input source */
	TRACE_RT_ERF_META	=21,/**< Metadata for a ERF input source */

	/** Not actually used - all DATA types begin from this value */
	TRACE_RT_DATA_SIMPLE	= 1000, 
	
	/** RT is encapsulating an ERF capture record */
	TRACE_RT_DATA_ERF	=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_ERF, 
	/** RT is encapsulating a WAG capture record */
	TRACE_RT_DATA_WAG	=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_WAG, 
	/** RT is encapsulating a Legacy ATM capture record */
	TRACE_RT_DATA_LEGACY_ATM=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_LEGACY_ATM, 
	/** RT is encapsulating a Legacy POS capture record */
	TRACE_RT_DATA_LEGACY_POS=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_LEGACY_POS, 
	/** RT is encapsulating a Legacy ETH capture record */
	TRACE_RT_DATA_LEGACY_ETH=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_LEGACY_ETH, 
	/** RT is encapsulating a Linux native capture record */
	TRACE_RT_DATA_LINUX_NATIVE=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_LINUX_NATIVE,
	/** RT is encapsulating a BSD native capture record */
	//TRACE_RT_DATA_BPF       =TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_BPF,
	/** RT is encapsulating a TSH capture record */
	TRACE_RT_DATA_TSH	=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_TSH,
	/** RT is encapsulating an ATM header capture record */
	TRACE_RT_DATA_ATMHDR = TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_ATMHDR,
	/** RT is encapsulating a Legacy NZIX capture record */
	TRACE_RT_DATA_LEGACY_NZIX=TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_LEGACY_NZIX,
	/** RT is encapsulating a Linux native PACKET_MMAP capture record */
	TRACE_RT_DATA_LINUX_RING=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_LINUX_RING,
	/** RT is encapsulating a Intel DPDK capture record */
	TRACE_RT_DATA_DPDK=TRACE_RT_DATA_SIMPLE+TRACE_FORMAT_DPDK,
	/** RT is encapsulating a etsilive capture record */
        TRACE_RT_DATA_ETSILI = TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_ETSILIVE,
	/** RT is encapsulating a tzsplive capture record */
	TRACE_RT_DATA_TZSP = TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_TZSPLIVE,
	/** RT is encapsulating a packet tagged by corsarotagger */
	TRACE_RT_DATA_CORSARO_TAGGED = TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_CORSAROTAG,
        /** RT is encapsulating a packet tagged by AF_XDP */
        TRACE_RT_DATA_XDP = TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_XDP,

	/** RT is encapsulating a PF_RING capture record */
	TRACE_RT_DATA_PFRINGOLD = TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_PFRINGOLD,
	TRACE_RT_DATA_PFRING = TRACE_RT_DATA_SIMPLE + TRACE_FORMAT_PFRING,

	/** As PCAP does not store the linktype with the packet, we need to 
	 * create a separate RT type for each supported DLT, starting from
	 * this value */
	TRACE_RT_DATA_DLT		= 2000, 
	/** RT is encapsulating a PCAP capture record with a NULL linktype */ 
	TRACE_RT_DLT_NULL		=TRACE_RT_DATA_DLT+TRACE_DLT_NULL,
	/** RT is encapsulating a PCAP capture record with an Ethernet 
	 * linktype */ 
	TRACE_RT_DLT_EN10MB		=TRACE_RT_DATA_DLT+TRACE_DLT_EN10MB,
	/** RT is encapsulating a PCAP capture record with an 802.11 
	 * linktype */ 
	TRACE_RT_DLT_IEEE802_11		=TRACE_RT_DATA_DLT+TRACE_DLT_IEEE802_11,
	/** RT is encapsulating a PCAP capture record with a Linux SLL 
	 * linktype */ 
	TRACE_RT_DLT_LINUX_SLL		=TRACE_RT_DATA_DLT+TRACE_DLT_LINUX_SLL,
	/** RT is encapsulating a PCAP capture record with a PFlog linktype */ 
	TRACE_RT_DLT_PFLOG		=TRACE_RT_DATA_DLT+TRACE_DLT_PFLOG,
	/** RT is encapsulating a PCAP capture record with an AAL5 linktype */ 
	TRACE_RT_DLT_ATM_RFC1483 	=TRACE_RT_DATA_DLT+TRACE_DLT_ATM_RFC1483,
	/** Unused value marking the end of the valid range for PCAP RT 
	 * encapsulation */
	TRACE_RT_DATA_DLT_END		= 2999,
	/** BPF does not store the linktype with the packet, so we need a
	 * separate RT type for each supported DLT. This value represents the
	 * starting point */
	TRACE_RT_DATA_BPF		= 3000,

	TRACE_RT_BPF_NULL		= TRACE_RT_DATA_BPF+TRACE_DLT_NULL,
	TRACE_RT_BPF_EN10MB		= TRACE_RT_DATA_BPF+TRACE_DLT_EN10MB,
	TRACE_RT_BPF_IEEE802_11		= TRACE_RT_DATA_BPF+TRACE_DLT_IEEE802_11,
	TRACE_RT_BPF_PFLOG		=TRACE_RT_DATA_BPF+TRACE_DLT_PFLOG,
	TRACE_RT_BPF_ATM_RFC1483 	=TRACE_RT_DATA_BPF+TRACE_DLT_ATM_RFC1483,

	TRACE_RT_DATA_BPF_END		= 3999,

        TRACE_RT_DATA_PCAPNG            = 4000,
	TRACE_RT_DATA_PCAPNG_END        = 4499,


	/** Unused value marking the end of the valid range for all RT packet
	 * types */
	TRACE_RT_LAST			= 5001
} libtrace_rt_types_t;

/** IP Protocol values */
typedef enum {
	TRACE_IPPROTO_IP	= 0,	/**< IP pseudo protocol number */
	TRACE_IPPROTO_ICMP	= 1,	/**< Internet Control Message protocol */
	TRACE_IPPROTO_IGMP	= 2,	/**< Internet Group Management Protocol */
	TRACE_IPPROTO_IPIP	= 4,	/**< IP encapsulated in IP */
	TRACE_IPPROTO_TCP	= 6,	/**< Transmission Control Protocol */
	TRACE_IPPROTO_UDP	= 17,	/**< User Datagram Protocol */
	TRACE_IPPROTO_IPV6	= 41,	/**< IPv6 over IPv4 */
	TRACE_IPPROTO_ROUTING	= 43,	/**< IPv6 Routing header */
	TRACE_IPPROTO_FRAGMENT	= 44,	/**< IPv6 Fragmentation header */
	TRACE_IPPROTO_RSVP	= 46,	/**< Resource Reservation Protocol */
	TRACE_IPPROTO_GRE	= 47,	/**< General Routing Encapsulation */
	TRACE_IPPROTO_ESP	= 50,	/**< Encapsulated Security Payload [RFC2406] */
	TRACE_IPPROTO_AH	= 51,	/**< Authentication Header [RFC2402] */
	TRACE_IPPROTO_ICMPV6	= 58,	/**< ICMPv6 */
	TRACE_IPPROTO_NONE	= 59,	/**< IPv6 no next header */
	TRACE_IPPROTO_DSTOPTS	= 60,	/**< IPv6 destination options */
	TRACE_IPPROTO_OSPF	= 89,	/**< Open Shortest Path First routing protocol */
	TRACE_IPPROTO_PIM	= 103,	/**< Protocol Independant Multicast */
	TRACE_IPPROTO_SCTP	= 132	/**< Stream Control Transmission Protocol */
} libtrace_ipproto_t;

/** Ethertypes supported by Libtrace */
typedef enum {
	/* Numbers <=1500 are of course, LLC/SNAP */
	TRACE_ETHERTYPE_LOOPBACK= 0x0060,	/**< Ethernet Loopback */
	TRACE_ETHERTYPE_IP	= 0x0800,	/**< IPv4 */
	TRACE_ETHERTYPE_ARP	= 0x0806,	/**< Address resolution protocol */
	TRACE_ETHERTYPE_RARP	= 0x8035,	/**< Reverse ARP */
	TRACE_ETHERTYPE_8021Q	= 0x8100,	/**< 802.1q VLAN Extended Header */
	TRACE_ETHERTYPE_8021QS	= 0x88A8,	/**< 802.1q Service VLAN tag */
	TRACE_ETHERTYPE_IPV6	= 0x86DD,	/**< IPv6 */
	TRACE_ETHERTYPE_MPLS	= 0x8847,	/**< MPLS Unicast traffic */
	TRACE_ETHERTYPE_MPLS_MC = 0x8848,	/**< MPLS Multicast traffic */
	TRACE_ETHERTYPE_PPP_DISC= 0x8863,	/**< PPPoE Service Discovery */
	TRACE_ETHERTYPE_PPP_SES = 0x8864,	/**< PPPoE Session Messages */
	TRACE_ETHERTYPE_8021X   = 0x888E,	/**< 802.1X Authentication */
	TRACE_ETHERTYPE_PPP     = 0x880B    /**< PPP */
} libtrace_ethertype_t;

/** constant to check if a vlan was found */
#define VLAN_NOT_FOUND 0xFFFF

/** constant to check if a mpls label was found */
#define MPLS_NOT_FOUND 0xFFFFFFFF

typedef struct libtrace_layer2_header {
        uint16_t ethertype;                     /**< Ethertype of the header */
        void *data;                             /**< Pointer to the header */
} libtrace_layer2_header_t;
typedef struct libtrace_layer2_headers {
        uint64_t bitmask;			/**< Bitmask of found headers */
        int num;				/**< The number of header */
        libtrace_layer2_header_t *header;	/**< Array of all found layer2 headers */
} libtrace_layer2_headers_t;
/** Enumeration of bitmask layer2 headers within libtrace_layer2_headers_t */
enum {
	TRACE_BITMASK_LOOPBACK	= 1,
	TRACE_BITMASK_IP	= 2,
	TRACE_BITMASK_ARP	= 4,
	TRACE_BITMASK_RARP	= 8,
	TRACE_BITMASK_8021Q	= 16,
	TRACE_BITMASK_IPV6	= 32,
	TRACE_BITMASK_8021QS	= 64,
	TRACE_BITMASK_MPLS	= 128,
	TRACE_BITMASK_MPLS_MC	= 256,
	TRACE_BITMASK_PPP_DISC	= 512,
	TRACE_BITMASK_PPP_SES	= 1024,
};

/** Enumeration of datatype returned inside libtrace_meta_item_t structure */
typedef enum {
	TRACE_META_UINT8	= 1,
        TRACE_META_UINT32	= 2,        
        TRACE_META_UINT64	= 3,
        TRACE_META_STRING       = 4,
        TRACE_META_UNKNOWN      = 5,
	TRACE_META_IPV4		= 6,
	TRACE_META_IPV6		= 7,
	TRACE_META_MAC		= 8, 
} libtrace_meta_datatype_t;

/** A structure representing a single meta-data field */
typedef struct libtrace_meta_item {
        /** Identifier for the section / block that this meta-data came from */
	uint16_t section;

        /** Identifier for the meta-data field itself */
        uint16_t option;

        /** Label string for this meta-data field */
	char *option_name;

        /** The length of the meta-data value (in bytes) */
        uint16_t len;

        /** The 'type' for the meta-data value, e.g. string, unsigned int */
        libtrace_meta_datatype_t datatype;

        /** A pointer to the meta-data value -- you will need to cast
         *  appropriately based based on the value of 'datatype'.
         */
        void *data;
} libtrace_meta_item_t;

/** A collection of meta-data fields */
typedef struct libtrace_meta_section {
        /** Number of meta-data fields in this collection */
	uint16_t num;

        /** Pointer to the array containing the meta-data fields for this
         *  collection.
         */
	libtrace_meta_item_t *items;
} libtrace_meta_t;

typedef struct libtrace_packet_cache {
	int capture_length;		/**< Cached capture length */
	int wire_length;		/**< Cached wire length */
	int payload_length;		/**< Cached payload length */
        int framing_length;             /**< Cached framing length */
	void *l2_header;		/**< Cached link header */
	libtrace_linktype_t link_type;	/**< Cached link type */
	uint32_t l2_remaining;		/**< Cached link remaining */
	void *l3_header;		/**< Cached l3 header */
	uint16_t l3_ethertype;		/**< Cached l3 ethertype */
	uint32_t l3_remaining;		/**< Cached l3 remaining */
	void *l4_header;		/**< Cached transport header */
	uint8_t transport_proto;	/**< Cached transport protocol */
	uint32_t l4_remaining;		/**< Cached transport remaining */
} libtrace_packet_cache_t;

/** The libtrace packet structure. Applications shouldn't be 
 * meddling around in here 
 */
typedef struct libtrace_packet_t {
	struct libtrace_t *trace;       /**< Pointer to the trace */
	void *header;			/**< Pointer to the framing header */
	void *payload;			/**< Pointer to the link layer */
	void *buffer;			/**< Allocated buffer */
	libtrace_rt_types_t  type;      /**< RT protocol type for the packet */
	buf_control_t buf_control;      /**< Describes memory ownership */
        libtrace_packet_cache_t cached; /**< Cached packet properties / headers */
	uint64_t order;                 /**< Notes the order of this packet in relation to the input */
	uint64_t hash;                  /**< A hash of the packet as supplied by the user */
	int error;                      /**< The error status of pread_packet */
        uint64_t internalid;            /** Internal identifier for the pkt */
        void *srcbucket;                /** Source bucket in trace_rt */
        void *fmtdata;                  /**< Storage for format-specific data */
        pthread_mutex_t ref_lock;       /**< Lock for reference counter */
        int refcount;                   /**< Reference counter */
        int which_trace_start;          /**< Used to match packet to a started instance of the parent trace */
} libtrace_packet_t;

#define IS_LIBTRACE_META_PACKET(packet) (packet->type < TRACE_RT_DATA_SIMPLE)


/** Trace directions. 
 * Note that these are the directions used by convention. More directions 
 * are possible, not just these 3, and that they may not conform to this
 * convention.
 */
typedef enum {
	TRACE_DIR_OUTGOING = 0,		/**< Packets originating "inside" */
	TRACE_DIR_INCOMING = 1,		/**< Packets originating "outside" */
	TRACE_DIR_OTHER	   = 2,		/**< Packets with an unknown direction, or one that's unknown */
	TRACE_DIR_UNKNOWN = -1,		/**< No direction information available */
} libtrace_direction_t;

/** Enumeration of Radiotap fields */
typedef enum {
    TRACE_RADIOTAP_TSFT = 0, /**< Timer synchronisation function, in microseconds (uint64) */
    TRACE_RADIOTAP_FLAGS = 1, /**< Wireless flags (uint8) */
    TRACE_RADIOTAP_RATE = 2, /**< Bitrate in units of 500kbps (uint8) */
    TRACE_RADIOTAP_CHANNEL = 3, /**< Frequency in MHz (uint16) and channel flags (uint16) */
    TRACE_RADIOTAP_FHSS = 4, /**< FHSS hop set (uint8) and hopping pattern (uint8) */
    TRACE_RADIOTAP_DBM_ANTSIGNAL = 5, /**< Signal power in dBm (int8) */
    TRACE_RADIOTAP_DBM_ANTNOISE = 6, /**< Noise power in dBm (int8) */
    TRACE_RADIOTAP_LOCK_QUALITY = 7, /**< Barker Code lock quality (uint16) */
    TRACE_RADIOTAP_TX_ATTENUATION = 8, /**< TX attenuation as unitless distance from max power (uint16) */
    TRACE_RADIOTAP_DB_TX_ATTENUATION = 9, /**< TX attenuation as dB from max power (uint16) */
    TRACE_RADIOTAP_DBM_TX_POWER = 10, /**< TX Power in dBm (int8) */
    TRACE_RADIOTAP_ANTENNA = 11, /**< Antenna frame was rx'd or tx'd on (uint8) */
    TRACE_RADIOTAP_DB_ANTSIGNAL = 12, /**< Signal power in dB from a fixed reference (uint8) */
    TRACE_RADIOTAP_DB_ANTNOISE = 13, /**< Noise power in dB from a fixed reference (uint8) */
    TRACE_RADIOTAP_RX_FLAGS = 14, /** Properties of received frame (uint16) */
    TRACE_RADIOTAP_TX_FLAGS = 15, /** Properties of transmitted frame (uint16) */
    TRACE_RADIOTAP_RTS_RETRIES = 16, /** Number of rts retries frame used (uint8) */
    TRACE_RADIOTAP_DATA_RETRIES = 17, /** Number of unicast retries a transmitted frame used (uint8) */
    TRACE_RADIOTAP_EXT = 31
} libtrace_radiotap_field_t;


/** @name Protocol structures
 * These convenience structures provide portable versions of the headers
 * for a variety of protocols.
 * @{
 */

#ifdef WIN32
#pragma pack(push)
#pragma pack(1)
#endif

/** Generic IP header structure */
typedef struct libtrace_ip
{
#if __BYTE_ORDER == __LITTLE_ENDIAN
    LT_BITFIELD8 ip_hl:4;		/**< Header Length */
    LT_BITFIELD8 ip_v:4;		/**< Version */
#elif __BYTE_ORDER == __BIG_ENDIAN
    LT_BITFIELD8 ip_v:4;		/**< Version */
    LT_BITFIELD8 ip_hl:4;		/**< Header Length */
#else
#   error "Adjust your <bits/endian.h> defines"
#endif
    uint8_t  ip_tos;			/**< Type of Service */
    uint16_t ip_len;			/**< Total Length */
    uint16_t  ip_id;			/**< Identification */
    uint16_t ip_off;			/**< IP Fragment offset (and flags) */
    uint8_t  ip_ttl;			/**< Time to Live */
    uint8_t  ip_p;			/**< Protocol */
    uint16_t ip_sum;			/**< Checksum */
    struct in_addr ip_src;		/**< Source Address */
    struct in_addr ip_dst;		/**< Destination Address */
} PACKED libtrace_ip_t;
ct_assert(sizeof(libtrace_ip_t) == 20);

/** IPv6 header extension structure */
typedef struct libtrace_ip6_ext
{
	uint8_t nxt;	/**< Next header */
	uint8_t len;	/**< Length of the current header */
} PACKED libtrace_ip6_ext_t;
ct_assert(sizeof(libtrace_ip6_ext_t) == 2);

/** IPv6 fragmentation header */
typedef struct libtrace_ip6_frag 
{
	uint8_t nxt;	/**< Next header */
	uint8_t res;	/**< Reserved */
	uint16_t frag_off;	/**< Fragment Offset (includes M flag) */
	uint32_t ident;	/** Fragment identification */
} PACKED libtrace_ip6_frag_t;
ct_assert(sizeof(libtrace_ip6_frag_t) == 8);

/** Generic IPv6 header structure
 *
 * @note The flow label field also includes the Version and Traffic Class
 * fields, because we haven't figured out a nice way to deal with fields
 * crossing byte boundaries on both Big and Little Endian machines */
typedef struct libtrace_ip6
{ 
    uint32_t flow;			/**< Flow label */
    uint16_t plen;			/**< Payload length */
    uint8_t nxt;			/**< Next header */
    uint8_t hlim;			/**< Hop limit */
    struct in6_addr ip_src;		/**< Source address */
    struct in6_addr ip_dst;		/**< Destination address */
} PACKED libtrace_ip6_t;
ct_assert(sizeof(libtrace_ip6_t) == 40);

/** Generic TCP header structure */
typedef struct libtrace_tcp
  {
    uint16_t source;		/**< Source Port */
    uint16_t dest;		/**< Destination port */
    uint32_t seq;		/**< Sequence number */
    uint32_t ack_seq;		/**< Acknowledgement Number */
#  if __BYTE_ORDER == __LITTLE_ENDIAN
    LT_BITFIELD8 ecn_ns:1;      /**< ECN Nonce Sum */
    LT_BITFIELD8 res1:3;        /**< Reserved bits */
    LT_BITFIELD8 doff:4;        /**< Data Offset */
    LT_BITFIELD8 fin:1;         /**< FIN */
    LT_BITFIELD8 syn:1;         /**< SYN flag */
    LT_BITFIELD8 rst:1;         /**< RST flag */
    LT_BITFIELD8 psh:1;         /**< PuSH flag */
    LT_BITFIELD8 ack:1;         /**< ACK flag */
    LT_BITFIELD8 urg:1;         /**< URG flag */
    LT_BITFIELD8 ece:1;         /**< ECN Echo */
    LT_BITFIELD8 cwr:1;         /**< ECN CWR */
#  elif __BYTE_ORDER == __BIG_ENDIAN
    LT_BITFIELD8 doff:4;        /**< Data offset */
    LT_BITFIELD8 res1:3;        /**< Reserved bits */
    LT_BITFIELD8 ecn_ns:1;      /**< ECN Nonce Sum */
    LT_BITFIELD8 cwr:1;         /**< ECN CWR */
    LT_BITFIELD8 ece:1;         /**< ECN Echo */
    LT_BITFIELD8 urg:1;         /**< URG flag */
    LT_BITFIELD8 ack:1;         /**< ACK flag */
    LT_BITFIELD8 psh:1;         /**< PuSH flag */
    LT_BITFIELD8 rst:1;         /**< RST flag */
    LT_BITFIELD8 syn:1;         /**< SYN flag */
    LT_BITFIELD8 fin:1;         /**< FIN flag */
#  else
#   error "Adjust your <bits/endian.h> defines"
#  endif
    uint16_t window;		/**< Window Size */
    uint16_t check;		/**< Checksum */
    uint16_t urg_ptr;		/**< Urgent Pointer */
} PACKED libtrace_tcp_t;
ct_assert(sizeof(libtrace_tcp_t) == 20);

/** Generic UDP header structure */
typedef struct libtrace_udp {
  uint16_t	source;		/**< Source port */
  uint16_t	dest;		/**< Destination port */
  uint16_t	len;		/**< Length */
  uint16_t	check;		/**< Checksum */
} PACKED libtrace_udp_t;
ct_assert(sizeof(libtrace_udp_t) == 8);

/** Generic ICMP header structure */
typedef struct libtrace_icmp
{
  uint8_t type;		/**< Message Type */
  uint8_t code;		/**< Type Sub-code */
  uint16_t checksum;		/**< Checksum */
  union
  {
    struct
    {
      uint16_t	id;		/**< ID of the Echo request */
      uint16_t	sequence;	/**< Sequence number of the Echo request */
    } echo;			/**< Echo Datagram */
    uint32_t	gateway;	/**< Gateway Address */
    struct
    {
      uint16_t	unused;		/**< Unused */
      uint16_t	mtu;		/**< Next-hop MTU */
    } frag;			/**< Path MTU Discovery */
  } un;				/**< Union for Payloads of Various ICMP Codes */
} PACKED libtrace_icmp_t;
 ct_assert(sizeof(libtrace_icmp_t) == 8);

/** Generic ICMPv6 header structure */
typedef struct libtrace_icmp6 {
  uint8_t type;		/**< Message Type */
  uint8_t code;		/**< Type Sub-code */
  uint16_t checksum;	/**< Checksum */

  union {
    struct {
	uint8_t length;	  /**< Length of original datagram content in 64 bit words */
	uint8_t unused;	  /**< Unused */	
	uint8_t unused1;  /**< Unused */
    } extend;	/**< Extensions added in RFC 4884 for Time Exceeded and Destination Unreachable Messages */

    uint32_t mtu;	/**< MTU from Packet Too Big Message */
    uint32_t pointer;	/**< Pointer from Parameter Problem Message */
    struct {
	uint16_t id;	/**< Echo Identifier */
	uint16_t sequence; /**< Echo Sequence Number */
    } echo; /**< Data required for Echo Request and Reply messages */
  } un;
} PACKED libtrace_icmp6_t;
ct_assert(sizeof(libtrace_icmp6_t) == 8);

/** Generic LLC/SNAP header structure */
typedef struct libtrace_llcsnap
{
/* LLC */
  uint8_t dsap;			/**< Destination Service Access Point */
  uint8_t ssap;			/**< Source Service Access Point */
  uint8_t control;		/**< Control field */
/* SNAP */
  LT_BITFIELD32 oui:24; /**< Organisationally Unique Identifier (scope)*/
  uint16_t type;		/**< Protocol within OUI */
} PACKED libtrace_llcsnap_t;
ct_assert(sizeof(libtrace_llcsnap_t) == 8);

/** 802.3 frame */
typedef struct libtrace_ether
{
  uint8_t ether_dhost[6];	/**< Destination Ether Addr */
  uint8_t ether_shost[6];	/**< Source Ether Addr */
  uint16_t ether_type;		/**< Packet Type ID Field (next-header) */
} PACKED libtrace_ether_t;
ct_assert(sizeof(libtrace_ether_t) == 14);

/** 802.1Q frame */
typedef struct libtrace_8021q 
{
    /* The tci field includes:
     * Priority code point - 3 bits
     * Drop eligible indicator - 1 bit
     * VLAN identifier - 12 bits
     * These fields are merged and can be extracted using the macro functions.
     * This is to deal with values crossing byte boundaries.
     */
    uint16_t tci;               /**< pri, cfi, id */
    uint16_t vlan_ether_type;   /**< VLAN Sub-packet Type ID Field 
                                  * (next-header)*/

    #define LT_VLAN_PCP(x) ((ntohs(x->tci) & 0xe000) >> 13)
    #define LT_VLAN_DEI(x) ((ntohs(x->tci) & 0x1000) >> 12)
    #define LT_VLAN_VID(x) (ntohs(x->tci) & 0xfff)
} PACKED libtrace_8021q_t;
ct_assert(sizeof(libtrace_8021q_t) == 4);

/** ATM User Network Interface (UNI) Cell. */
typedef struct libtrace_atm_cell
{
    /* This field contains
     * generic flow control (gfc) - 4 bits
     * virtual path identifier (vpi) - 8 bits
     * virtual channel identifier (vci) - 16 bits
     * payload type (pt) - 3 bits
     * cell loss priority (clp) - 1 bit
     * These fields are merged and can be extracted using the macro functions.
     * This is to deal with values crossing byte boundaries.
     */
    uint32_t gfc_vpi_vci_pt_clp;    /**< gfc, vpi, vci, pt, clp */
    uint8_t hec;                    /**< Header Error Control */

    #define LT_ATM_GFC(x) ((ntohl(x->gfc_vpi_vci_pt_clp) & 0xf0000000) >> 28)
    #define LT_ATM_VPI(x) ((ntohl(x->gfc_vpi_vci_pt_clp) & 0x0ff00000) >> 20)
    #define LT_ATM_VCI(x) ((ntohl(x->gfc_vpi_vci_pt_clp) & 0x0ffff0) >> 4)
    #define LT_ATM_PT(x) ((ntohl(x->gfc_vpi_vci_pt_clp) & 0x0e) >> 1)
    #define LT_ATM_CLP(x) (ntohl(x->gfc_vpi_vci_pt_clp) & 0x01)
} PACKED libtrace_atm_cell_t;
ct_assert(sizeof(libtrace_atm_cell_t) == 5);

/** ATM Network Node/Network Interface (NNI) Cell. */
typedef struct libtrace_atm_nni_cell
{
    /* This field contains
     * virtual path identifier (vpi) - 12 bits
     * virtual channel identifier (vci) - 16 bits
     * payload type (pt) - 3 bits
     * cell loss priority (clp) - 1 bit
     * These fields are merged and can be extracted using the macro functions.
     * This is to deal with values crossing byte boundaries.
     */
    uint32_t vpi_vci_pt_clp;    /**< vpi, vci, pt, clp */
    uint8_t hec;                /**< Header Error Control */

    #define LT_ATM_NNI_VPI(x) ((ntohl(x->vpi_vci_pt_clp) & 0xfff00000) >> 20)
    #define LT_ATM_NNI_VCI(x) ((ntohl(x->vpi_vci_pt_clp) & 0x0ffff0) >> 4)
    #define LT_ATM_NNI_PT(x) ((ntohl(x->vpi_vci_pt_clp) & 0x0e) >> 1)
    #define LT_ATM_NNI_CLP(x) (ntohl(x->vpi_vci_pt_clp) & 0x01)
} PACKED libtrace_atm_nni_cell_t;
ct_assert(sizeof(libtrace_atm_nni_cell_t) == 5);

/** Captured UNI cell.
 *
 * Endace don't capture the HEC, presumably to keep alignment.  This 
 * version of the \ref libtrace_atm_cell is used when dealing with DAG 
 * captures of uni cells.
 *
 */
typedef struct libtrace_atm_capture_cell
{
    /* This field contains
     * generic flow control (gfc) - 4 bits
     * virtual path identifier (vpi) - 8 bits
     * virtual channel identifier (vci) - 16 bits
     * payload type (pt) - 3 bits
     * cell loss priority (clp) - 1 bit
     * These fields are merged and can be extracted using the macro functions.
     * This is to deal with values crossing byte boundaries.
     */
    uint32_t gfc_vpi_vci_pt_clp;    /**< gfc, vpi, vci, pt, clp */

    /* use macro functions in libtrace_atm_cell_t to extract
     * gfc, vpi, vci, pt and clp.
     */
} PACKED libtrace_atm_capture_cell_t;
ct_assert(sizeof(libtrace_atm_capture_cell_t) == 4);

/** Captured NNI cell.
 *
 * Endace don't capture the HEC, presumably to keep alignment.  This 
 * version of the \ref libtrace_atm_nni_cell is used when dealing with DAG
 * captures of nni cells.
 *
 */
typedef struct libtrace_atm_nni_capture_cell
{
    /* This field contains
     * virtual path identifier (vpi) - 12 bits
     * virtual channel identifier (vci) - 16 bits
     * payload type (pt) - 3 bits
     * cell loss priority (clp) - 1 bit
     * These fields are merged and can be extracted using the macro functions.
     * This is to deal with values crossing byte boundaries.
     */
    uint32_t vpi_vci_pt_clp;    /**< vpi, vci, pt, clp */
    uint8_t hec;                /**< Header Error Control */

    /* use macro functions in libtrace_atm_nni_cell_t to extract
     * vpi, vci, pt and clp
     */
} PACKED libtrace_atm_nni_capture_cell_t;
ct_assert(sizeof(libtrace_atm_nni_capture_cell_t) == 5);

/** PPP header */
typedef struct libtrace_ppp
{
 /* I can't figure out where the hell these two variables come from. They're
  * definitely not in RFC 1661 which defines PPP. Probably some weird thing
  * relating to the lack of distinction between PPP, HDLC and CHDLC */
	
/* uint8_t address; */		/**< PPP Address (0xFF - All stations) */
/* uint8_t header;  */		/**< PPP Control (0x03 - Unnumbered info) */
 uint16_t protocol;		/**< PPP Protocol (htons(0x0021) - IPv4 */
} PACKED libtrace_ppp_t;
ct_assert(sizeof(libtrace_ppp_t) == 2);

/** PPPoE header */
typedef struct libtrace_pppoe
{
#if __BYTE_ORDER == __LITTLE_ENDIAN
 LT_BITFIELD8 type:4;		/**< PPPoE Type */
 LT_BITFIELD8 version:4;	/**< Protocol version number */
#else
 LT_BITFIELD8 version:4;	/**< Protocol version number */
 LT_BITFIELD8 type:4;		/**< PPPoE Type */
#endif
 uint8_t code;			/**< PPPoE Code */
 uint16_t session_id;		/**< Session Identifier */
 uint16_t length;		/**< Total Length of the PPP packet */
} PACKED libtrace_pppoe_t;
ct_assert(sizeof(libtrace_pppoe_t) == 6);

/** Libtrace local definition of GRE (Generalised Routing Protocol) header
 * RFC2890
 */
typedef struct libtrace_gre_t
{
    uint16_t flags;         /**< Flags and version */
    uint16_t ethertype;     /**< Payload ethertype */
    uint16_t checksum;      /**< Optional checksum */
    uint16_t reserved1;     /**< Optional reserved */
    uint16_t key;           /**< Optional key (or Tenant Network ID) */
    uint16_t seq;           /**< Optional sequence number */
} PACKED libtrace_gre_t;
ct_assert(sizeof(libtrace_gre_t) == 12);

#define LIBTRACE_GRE_FLAG_CHECKSUM 0x8000
#define LIBTRACE_GRE_FLAG_KEY      0x2000
#define LIBTRACE_GRE_FLAG_SEQ      0x1000
#define LIBTRACE_GRE_FLAG_VERMASK  0x0007


/* PPTP GRE (RFC2637) */
#define LIBTRACE_GRE_FLAG_ACK 	   0x0080
#define LIBTRACE_GRE_PPTP_VERSION  0x0001

/** Libtrace local definition of VXLAN Header
 * (draft-mahalingam-dutt-dcops-vxlan)
 */
typedef struct libtrace_vxlan_t
{
    uint8_t flags;          /**< Flags */
    uint8_t reserved1[3];   /**< Reserved */
    uint8_t vni[3];         /**< VXLAN Network Identifier (VNI) */
    uint8_t reserved2;
} PACKED libtrace_vxlan_t;
ct_assert(sizeof(libtrace_vxlan_t) == 8);

/** 802.11 header */
typedef struct libtrace_80211_t {
#if __BYTE_ORDER == __LITTLE_ENDIAN
        LT_BITFIELD32      protocol:2;	/**< Protocol Version */
        LT_BITFIELD32      type:2;	/**< Frame Type */
        LT_BITFIELD32      subtype:4;	/**< Frame Subtype */
#else
	LT_BITFIELD32	   subtype:4;	/**< Frame Subtype */
	LT_BITFIELD32      type:2;	/**< Frame Type */
	LT_BITFIELD32      protocol:2;	/**< Protocol Version */
#endif

#if __BYTE_ORDER == __LITTLE_ENDIAN
        LT_BITFIELD32      to_ds:1;	/**< Packet to Distribution Service */
        LT_BITFIELD32      from_ds:1;	/**< Packet from Distribution Service */
        LT_BITFIELD32      more_frag:1;	/**< Packet has more fragments */
        LT_BITFIELD32      retry:1;	/**< Packet is a retry */
        LT_BITFIELD32      power:1;	/**< Power Management mode */
        LT_BITFIELD32      more_data:1;	/**< More data is buffered at station */
        LT_BITFIELD32      wep:1;	/**< WEP encryption indicator */
        LT_BITFIELD32      order:1;	/**< Strictly-Ordered class indicator */
#else
        LT_BITFIELD32      order:1;	/**< Strictly-Ordered class indicator */
        LT_BITFIELD32      wep:1;	/**< WEP encryption indicator */
        LT_BITFIELD32      more_data:1;	/**< More data is buffered at station */
        LT_BITFIELD32      power:1;	/**< Power Management mode */
        LT_BITFIELD32      retry:1;	/**< Packet is a retry */
        LT_BITFIELD32      more_frag:1;	/**< Packet has more fragments */
        LT_BITFIELD32      from_ds:1;	/**< Packet from Distribution Service */
        LT_BITFIELD32      to_ds:1;	/**< Packet to Distribution Service */
#endif
	
        uint16_t     duration;	/**< Duration value for NAV calculation */
        uint8_t      mac1[6];	/**< MAC Address 1 */
        uint8_t      mac2[6];	/**< MAC Address 2 */
        uint8_t      mac3[6];	/**< MAC Address 3 */
        uint16_t     SeqCtl;	/**< Sequence Control */	
        uint8_t      mac4[6];	/**< MAC Address 4 */
} PACKED libtrace_80211_t;
ct_assert(sizeof(libtrace_80211_t) == 30);

/** The Radiotap header pre-amble
 *
 * All Radiotap headers start with this pre-amble, followed by the fields
 * specified in the it_present bitmask. If bit 31 of it_present is set, then
 * another bitmask follows.
 * @note All of the radiotap data fields are in little-endian byte-order.
 */
typedef struct libtrace_radiotap_t {
    uint8_t     it_version; /**< Radiotap version */
    uint8_t     it_pad; /**< Padding for natural alignment */
    uint16_t    it_len; /**< Length in bytes of the entire Radiotap header */
    uint32_t    it_present; /**< Which Radiotap fields are present */
} PACKED libtrace_radiotap_t;
ct_assert(sizeof(libtrace_radiotap_t) == 8);

/** OSPF header */
typedef struct libtrace_ospf_v2_t
{
	uint8_t ospf_v;		/**< OSPF Version, should be 2 */
	uint8_t type;		/**< OSPF Packet Type */
	uint16_t ospf_len;	/**< Packet length, including OSPF header */
	struct in_addr router;	/**< Router ID of the packet source */
	struct in_addr area;	/**< Area the packet belongs to */
	uint16_t sum;		/**< Checksum */
	uint16_t au_type;	/**< Authentication procedure */
	uint16_t zero;		/**< Always zero */
	uint8_t au_key_id;	/**< Authentication Key ID */
	uint8_t au_data_len;	/**< Authentication Data Length */
	uint32_t au_seq_num;	/**< Cryptographic Sequence Number */
} PACKED libtrace_ospf_v2_t;
ct_assert(sizeof(libtrace_ospf_v2_t) == 24);

/** Options Field present in some OSPFv2 packets */
typedef struct libtrace_ospf_options_t {
#if __BYTE_ORDER == __LITTLE_ENDIAN
	LT_BITFIELD8 unused1:1;
	LT_BITFIELD8 e_bit:1;
	LT_BITFIELD8 mc_bit:1;
	LT_BITFIELD8 np_bit:1;
	LT_BITFIELD8 ea_bit:1;
	LT_BITFIELD8 dc_bit:1;
	LT_BITFIELD8 unused2:2;
#elif __BYTE_ORDER == __BIG_ENDIAN
	LT_BITFIELD8 unused2:2;
	LT_BITFIELD8 dc_bit:1;
	LT_BITFIELD8 ea_bit:1;
	LT_BITFIELD8 np_bit:1;
	LT_BITFIELD8 mc_bit:1;
	LT_BITFIELD8 e_bit:1;
	LT_BITFIELD8 unused1:1;
#endif
} PACKED libtrace_ospf_options_t;
ct_assert(sizeof(libtrace_ospf_options_t) == 1);

/** LSA Header for OSPFv2 */
typedef struct libtrace_ospf_lsa_v2_t
{
	uint16_t age;		/**< Time in seconds since LSA originated */
	libtrace_ospf_options_t lsa_options;	/**< Options */
	uint8_t lsa_type;	/**< LSA type */
	struct in_addr ls_id;	/**< Link State ID */
	struct in_addr adv_router; /**< Router that originated this LSA */
	uint32_t seq;		/**< LS sequence number */
	uint16_t checksum;	/**< Checksum */ 
	uint16_t length;	/**< Length of the LSA including LSA header */
} PACKED libtrace_ospf_lsa_v2_t;
ct_assert(sizeof(libtrace_ospf_lsa_v2_t) == 20);

/** OSPFv2 Hello Packet */
typedef struct libtrace_ospf_hello_v2_t
{
	struct in_addr mask;	/**< Network mask for this interface */
	uint16_t interval;	/**< Interval between Hello packets (secs) */
	libtrace_ospf_options_t hello_options;	/**< Options */
	uint8_t priority;	/**< Router Priority */
	uint32_t deadint;	/**< Interval before declaring a router down */
	struct in_addr designated;	/**< Designated router for the network */
	struct in_addr backup;	/**< Backup designated router */

	/** Neighbors follow from here, but there can be anywhere from 1 to N
	 * neighbors so I can't include that here */
} PACKED libtrace_ospf_hello_v2_t;
ct_assert(sizeof(libtrace_ospf_hello_v2_t) == 20);

/** OSPFv2 Database Description packet */
typedef struct libtrace_ospf_db_desc_v2_t
{
	uint16_t mtu;		/**< Interface MTU */
	libtrace_ospf_options_t db_desc_options;	/**< Options */
#if __BYTE_ORDER == __LITTLE_ENDIAN
	LT_BITFIELD8 db_desc_ms:1;	/**< If set, this router is the master */
	LT_BITFIELD8 db_desc_m:1;	/**< If set, more packets to follow */
	LT_BITFIELD8 db_desc_i:1;	/**< If set, this is the first packet in sequence */
	LT_BITFIELD8 zero:5;
#elif __BYTE_ORDER == __BIG_ENDIAN
	LT_BITFIELD8 zero:5;
	LT_BITFIELD8 db_desc_i:1;	/**< If set, this is the first packet in sequence */
	LT_BITFIELD8 db_desc_m:1;	/**< If set, more packets to follow */
	LT_BITFIELD8 db_desc_ms:1;	/**< If set, this router is the master */
#endif
	uint32_t seq;		/**< Sequence number for DD packets */
} PACKED libtrace_ospf_db_desc_v2_t;
ct_assert(sizeof(libtrace_ospf_db_desc_v2_t) == 8);

/** OSPF Link State Request Packet */
typedef struct libtrace_ospf_ls_req_t
{
	uint32_t ls_type;	/**< Link State Type */
	uint32_t ls_id;		/**< Link State Id */
	uint32_t advertising_router;	/**< Advertising Router */
} PACKED libtrace_ospf_ls_req_t;
ct_assert(sizeof(libtrace_ospf_ls_req_t) == 12);

/** OSPF Link State Update Packet */
typedef struct libtrace_ospf_ls_update_t
{
	uint32_t ls_num_adv;	/**< Number of LSAs in this packet */

	/* Followed by LSAs, use API functions to access these */
} PACKED libtrace_ospf_ls_update_t;
ct_assert(sizeof(libtrace_ospf_ls_update_t) == 4);

/** OSPFv2 AS External LSA Body */
typedef struct libtrace_ospf_as_external_lsa_t
{
	struct in_addr netmask;	/**< Netmask for the destination */
#if __BYTE_ORDER == __LITTLE_ENDIAN
	LT_BITFIELD8 tos:7;
	LT_BITFIELD8 e:1;	/**< If set, metric is Type 2. Else, Type 1 */
#elif __BYTE_ORDER == __BIG_ENDIAN
	LT_BITFIELD8 e:1;	/**< If set, metric is Type 2. Else, Type 1 */
	LT_BITFIELD8 tos:7;
#endif
	uint8_t metric_a;	/**< Byte 1 of the Metric field */
	uint8_t metric_b;	/**< Byte 2 of the Metric field */
	uint8_t metric_c;	/**< Byte 3 of the Metric field */
	struct in_addr forwarding;	/**< Forwarding address */
	uint32_t external_tag;		/**< External Route Tag */
} PACKED libtrace_ospf_as_external_lsa_v2_t;
ct_assert(sizeof(libtrace_ospf_as_external_lsa_v2_t) == 16);

/** OSPFv2 Summary LSA Body */
typedef struct libtrace_ospf_summary_lsa
{
	struct in_addr netmask;	/**< Netmask for the destination */
	uint8_t zero;		/**< Always zero */
	uint8_t metric_a;	/**< Byte 1 of the Metric field */
	uint8_t metric_b;	/**< Byte 2 of the Metric field */
	uint8_t metric_c;	/**< Byte 3 of the Metric field */
	
} PACKED libtrace_ospf_summary_lsa_v2_t;
ct_assert(sizeof(libtrace_ospf_summary_lsa_v2_t) == 8);

/** OSPFv2 Network LSA Body */
typedef struct libtrace_ospf_network_lsa_t
{
	struct in_addr netmask;	/**< Netmask for the network */
	/* Followed by IDs of attached routers */
} PACKED libtrace_ospf_network_lsa_v2_t;
ct_assert(sizeof(libtrace_ospf_network_lsa_v2_t) == 4);

/** OSPFv2 Router Link structure */
typedef struct libtrace_ospf_link_t
{
	struct in_addr link_id;		/**< Object that link connects to */
	struct in_addr link_data;	/**< Link Data field */
	uint8_t type;			/**< Link Type */
	uint8_t num_tos;		/**< Number of TOS metrics */
	uint16_t tos_metric;		/**< Cost of router link */
} PACKED libtrace_ospf_link_v2_t;
ct_assert(sizeof(libtrace_ospf_link_v2_t) == 12);

/** OSPFv2 Router LSA */
typedef struct libtrace_ospf_router_lsa_t
{
#if __BYTE_ORDER == __LITTLE_ENDIAN
	LT_BITFIELD8 b:1;	/**< Area Border Router Flag */
	LT_BITFIELD8 e:1;	/**< External Router Flag */
	LT_BITFIELD8 v:1;	/**< Virtual Endpoint Flag */
	LT_BITFIELD8 zero:5;
#elif __BYTE_ORDER == __BIG_ENDIAN
	LT_BITFIELD8 zero:5;
	LT_BITFIELD8 v:1;	/**< Virtual Endpoint Flag */
	LT_BITFIELD8 e:1;	/**< External Router Flag */
	LT_BITFIELD8 b:1;	/**< Area Border Router Flag */
#endif
	uint8_t zero2;		/**< Always zero */
	uint16_t num_links;	/**< Number of links in LSA */
} PACKED libtrace_ospf_router_lsa_v2_t;
ct_assert(sizeof(libtrace_ospf_router_lsa_v2_t) == 4);

/** OSPF message types */
typedef enum {
	TRACE_OSPF_HELLO = 1,		/**< OSPF Hello */
	TRACE_OSPF_DATADESC = 2,	/**< OSPF Database Description */
	TRACE_OSPF_LSREQ = 3,		/**< OSPF Link State Request */
	TRACE_OSPF_LSUPDATE = 4,	/**< OSPF Link State Update */
	TRACE_OSPF_LSACK = 5		/**< OSPF Link State Acknowledgement */
} libtrace_ospf_types_t;

/** OSPF link state acknowledgement types */
typedef enum {
        TRACE_OSPF_LS_ROUTER = 1,	/**< OSPF Router LSA */
        TRACE_OSPF_LS_NETWORK = 2,	/**< OSPF Network LSA */
        TRACE_OSPF_LS_SUMMARY = 3,	/**< OSPF Summary LSA */
        TRACE_OSPF_LS_ASBR_SUMMARY = 4,	/**< OSPF Summary LSA (ASBR) */
        TRACE_OSPF_LS_EXTERNAL = 5	/**< OSPF AS External LSA */
} libtrace_ospf_ls_types_t;

/** A local definition of an SLL header */
typedef struct libtrace_sll_header_t {
        uint16_t pkttype;               /**< Packet type */
        uint16_t hatype;                /**< Link-layer address type */
        uint16_t halen;                 /**< Link-layer address length */
        unsigned char addr[8];          /**< Link-layer address */
        uint16_t protocol;              /**< Protocol */
} PACKED libtrace_sll_header_t;
ct_assert(sizeof(libtrace_sll_header_t) == 16);


/* SLL packet types */

/** Packet was addressed for the local host */
#define TRACE_SLL_HOST          0
/** Packet was addressed for a broadcast address */
#define TRACE_SLL_BROADCAST     1
/** Packet was addressed for a multicast address */
#define TRACE_SLL_MULTICAST     2
/** Packet was addressed for another host but was captured by a promiscuous
 * device */
#define TRACE_SLL_OTHERHOST     3
/** Packet originated from the local host */
#define TRACE_SLL_OUTGOING      4


#ifdef WIN32
#pragma pack(pop)
#endif


/*@}*/

/** Prints help information for libtrace 
 *
 * Function prints out some basic help information regarding libtrace,
 * and then prints out the help() function registered with each input module
 */
DLLEXPORT void trace_help(void);

/** Causes a libtrace reader to stop blocking whilst waiting on new packets
 * and immediately return EOF.
 *
 * This function is useful if you are handling signals within your libtrace
 * program. If a live source is not receiving any packets (or they are being
 * filtered), a call to trace_read_packet will result in an infinite loop as
 * it will block until a packet is received. Normally, a SIGINT would cause the
 * program to end and thus break the loop, but if you are handling the signal
 * yourself then that signal will never reach libtrace.
 *
 * Instead this function sets a global variable within libtrace that will 
 * cause a blocking live capture to break on the next internal timeout, 
 * allowing control to be returned to the user and their own signal handling
 * to kick in.
 */
DLLEXPORT void trace_interrupt(void); 

/** @name Trace management
 * These members deal with creating, configuring, starting, pausing and
 * cleaning up a trace object
 *@{
 */

/** Takes a uri and splits it into a format and uridata component. 
 * @param uri		The uri to be parsed
 * @param [out] format	A pointer that will be updated to point to an allocated
 * 			string holding the format component of the URI
 * @return NULL if an error occurred, otherwise return a pointer to the uridata
 * component
 *
 * @note The format component is strdup'd by this function, so be sure to free
 * it when you are done with the split URI. Similarly, do not pass a pointer
 * to an allocated string into this function as the 'format' parameter, as
 * that memory will be leaked and replaced with the strdup'd format.
 */
DLLEXPORT const char *trace_parse_uri(const char *uri, char **format);

/** Create an input trace from a URI
 * 
 * @param uri A valid libtrace URI to be opened
 * @return An opaque pointer to a libtrace_t
 *
 * Some valid URI's are:
 *  - erf:/path/to/erf/file
 *  - erf:-  (stdin)
 *  - dag:/dev/dagcard
 *  - pcapint:pcapinterface                (eg: pcap:eth0)
 *  - pcap:/path/to/pcap/file
 *  - pcap:-
 *  - rt:hostname
 *  - rt:hostname:port
 *
 *  If an error occurred when attempting to open the trace file, a
 *  trace is still returned so trace_is_err() should be called to find out
 *  if an error occurred. The trace is created in the configuration state, you 
 *  must call trace_start before attempting to read packets from the trace.
 */
DLLEXPORT libtrace_t *trace_create(const char *uri);

/** Creates a "dummy" trace file that has only the format type set.
 *
 * @param uri A valid (but fake) URI indicating the format of the dummy trace that is to be created.
 * @return An opaque pointer to a (sparsely initialised) libtrace_t
 *
 * Only the format portion of the uri parameter matters - the 'file' being
 * opened does not have to exist.
 *
 * @note IMPORTANT: Do not attempt to call trace_read_packet or other such 
 * functions with the dummy trace. Its intended purpose is to provide access
 * to the format functions where the original trace may no longer exist or is
 * not the correct format, e.g. reading ERF packets from an RT input.
 */
DLLEXPORT libtrace_t *trace_create_dead(const char *uri);

/** Creates a trace output file from a URI. 
 *
 * @param uri The uri string describing the output format and destination
 * @return An opaque pointer to a libtrace_output_t
 *
 * Valid URIs include:
 *  - erf:/path/to/erf/file
 *  - pcap:/path/to/pcap/file
 *
 *  If an error occurred when attempting to open the output trace, a trace is 
 *  still returned but trace_errno will be set. Use trace_is_err_out() and 
 *  trace_perror_output() to get more information.
 */
DLLEXPORT libtrace_out_t *trace_create_output(const char *uri);

/** Start an input trace
 * @param libtrace	The trace to start
 * @return 0 on success, -1 on failure
 *
 * This does the actual work of starting the input trace and applying
 * all the config options.  This may fail, returning -1. The libtrace error
 * handling functions can be used to get more information about what 
 * specifically went wrong.
 */
DLLEXPORT int trace_start(libtrace_t *libtrace);

/** Pauses an input trace
 * @param libtrace	The trace to pause
 * @return 0 on success, -1 on failure
 *
 * This stops an input trace that is in progress and returns you to the 
 * configuration state.  Any packets that arrive on a live capture after 
 * trace_pause() has been called will be discarded.  To resume the trace, call 
 * trace_start().
 */
DLLEXPORT int trace_pause(libtrace_t *libtrace);

/** Start an output trace
 * @param libtrace	The trace to start
 * @return 0 on success, -1 on failure
 *
 * This does the actual work with starting a trace capable of writing packets.  
 * This generally creates the output file.
 */
DLLEXPORT int trace_start_output(libtrace_out_t *libtrace);

/** Valid configuration options for input traces */
typedef enum {
	/** Maximum number of bytes to be captured for any given packet */
	TRACE_OPTION_SNAPLEN, 	

	/** If enabled, places a live capture interface into promiscuous mode */
	TRACE_OPTION_PROMISC, 	

	/** Apply this filter to all packets read from this trace */
	TRACE_OPTION_FILTER,  	

	/** Defines the frequency of meta-data reporting, e.g. DUCK packets */
	TRACE_OPTION_META_FREQ,	

	/** If enabled, the libtrace event API will ignore time gaps between
	 * packets when reading from a trace file */
	TRACE_OPTION_EVENT_REALTIME,

	/** The hasher function for a parallel libtrace. It is recommended to
	 * access this option via trace_set_hasher(). */
	TRACE_OPTION_HASHER,

	/** Speed up trace file replays (via trace_event()) by this factor */
	TRACE_OPTION_REPLAY_SPEEDUP,

	/** Always assume ERF framing length is the given value, rather than
	 *  trying to calculate it from the packet type. */
	TRACE_OPTION_CONSTANT_ERF_FRAMING,

	/** If enabled all meta packet will be discarded */
	TRACE_OPTION_DISCARD_META,

	/** Offload XDP program to hardware */
	TRACE_OPTION_XDP_HARDWARE_OFFLOAD,

	/** Install XDP program in native/driver mode */
	TRACE_OPTION_XDP_DRV_MODE,

	/** Install XDP program in SKB (generic) mode */
	TRACE_OPTION_XDP_SKB_MODE,

	/** Force XDP copy mode */
	TRACE_OPTION_XDP_ZERO_COPY_MODE,

	/** Force XDP zero copy mode */
	TRACE_OPTION_XDP_COPY_MODE,
} trace_option_t;

/** Sets an input config option
 * @param libtrace	The trace object to apply the option to
 * @param option	The option to set
 * @param value		The value to set the option to
 * @return -1 if option configuration failed, 0 otherwise
 *
 * This should be called after trace_create(), and before trace_start()
 *
 * @note Please consider using the newer trace_set_X() functions to access
 * this function.
 */
DLLEXPORT int trace_config(libtrace_t *libtrace,
		trace_option_t option,
		void *value);

/** Maximum number of bytes to be captured for any given packet
 *
 * @param libtrace The trace object to apply the option to
 * @param snaplen The snap length to set
 * @return -1 if option configuration failed, 0 otherwise
 */
DLLEXPORT int trace_set_snaplen(libtrace_t *trace, int snaplen);

/** If enabled, places a live capture interface into promiscuous mode
 *
 * @param libtrace The trace object to apply the option to
 * @param promisc
 * @return -1 if option configuration failed, 0 otherwise
 */
DLLEXPORT int trace_set_promisc(libtrace_t *trace, bool promisc);

/** Apply this filter to all packets read from this trace
 *
 * @param libtrace The trace object to apply the option to
 * @param filter The filter to apply
 * @return -1 if option configuration failed, 0 otherwise
 */
DLLEXPORT int trace_set_filter(libtrace_t *trace, libtrace_filter_t *filter);

/** Defines the frequency of meta-data reporting, e.g. DUCK packets
 *
 * @param libtrace The trace object to apply the option to
 * @param freq The meta data frequency
 * @return -1 if option configuration failed, 0 otherwise
 */
DLLEXPORT int trace_set_meta_freq(libtrace_t *trace, int freq);

/** If enabled, the libtrace event API will ignore time gaps between
 * packets when reading from a trace file.
 *
 * @param libtrace The trace object to apply the option to
 * @param realtime True ignores gaps
 * @return -1 if option configuration failed, 0 otherwise
 */
DLLEXPORT int trace_set_event_realtime(libtrace_t *trace, bool realtime);

/** Valid compression types 
 * Note, this must be kept in sync with WANDIO_COMPRESS_* numbers in wandio.h
 */ 
typedef enum {
	TRACE_OPTION_COMPRESSTYPE_NONE = 0, /**< No compression */
	TRACE_OPTION_COMPRESSTYPE_ZLIB = 1, /**< GZip Compression */
	TRACE_OPTION_COMPRESSTYPE_BZ2  = 2, /**< BZip2 Compression */
	TRACE_OPTION_COMPRESSTYPE_LZO  = 3,  /**< LZO Compression */
	TRACE_OPTION_COMPRESSTYPE_LZMA  = 4,  /**< LZMA Compression */
	TRACE_OPTION_COMPRESSTYPE_ZSTD  = 5,  /**< zstd Compression */
	TRACE_OPTION_COMPRESSTYPE_LZ4  = 6,  /**< lz4 Compression */
        TRACE_OPTION_COMPRESSTYPE_LAST
} trace_option_compresstype_t;

/** Valid configuration options for output traces */
typedef enum {
	/** File flags to use when opening an output file, e.g. O_APPEND */
	TRACE_OPTION_OUTPUT_FILEFLAGS,

	/** Compression level: 0 = no compression, 1 = faster compression,
	 * 9 = better compression */
	TRACE_OPTION_OUTPUT_COMPRESS,

	/** Compression type, see trace_option_compresstype_t */
	TRACE_OPTION_OUTPUT_COMPRESSTYPE,

	/** TX queue size **/
	TRACE_OPTION_TX_MAX_QUEUE

} trace_option_output_t;

/* To add a new stat field update this list, and the relevant places in
 * libtrace_stat_t structure.
 */
/** An X Macro set for libtrace stat fields */
#define LIBTRACE_STAT_FIELDS \
	X(accepted) \
	X(filtered) \
	X(received) \
	X(dropped) \
	X(captured) \
        X(missing) \
	X(errors)

/**
 * Statistic counters are cumulative from the time the trace is started.
 * Trace pause will reset the counters, to zero.
 * Always check \a{field}_valid is set before attempting to read the stored
 * value.
 *
 * @note Always allocate this structure using trace_create_statistics().
 *       This allows us to extend the structure in the future.
 */
typedef struct libtrace_stat_t {
#define X(name) LT_BITFIELD64 name ##_valid : 1;
	LIBTRACE_STAT_FIELDS
#undef X
	/* We use the remaining space as magic to ensure the structure
	 * was alloc'd by us. We can easily decrease the no. bits without
	 * problems as long as we update any asserts as needed */
	LT_BITFIELD64 reserved1: 25; /**< Bits reserved for future fields */
	LT_BITFIELD64 reserved2: 24; /**< Bits reserved for future fields */
	LT_BITFIELD64 magic: 8; /**< A number stored against the format to
				  ensure the struct was allocated correctly */

	/* These must all be uint64_t's, match this order with the X macro */
	/** The number of packets that have been read from the input trace
	 * using trace_read_packet(). In the parallel framework this may include
	 * some packets waiting in a batch yet to be seen by the user's
	 * application.
	 *
	 * This does not include filtered packets because these do not make it
	 * to trace_read_packet().
	 *
	 * @note This field replaces trace_get_accepted_packets()
	 */
	uint64_t accepted;

	/** The number of packets that were captured, but discarded for not
	 * matching a provided filter.
	 *
	 * @note This field replaces trace_get_filtered_packets()
	 */
	uint64_t filtered;

	/** The total number of good packets which have been received. Including
	 * those which are dropped and filtered. This does not include errors.
	 *
	 * @note This may include a small number of buffered packets
	 *       not yet included in accepted.
	 *
	 * @note This field replaces trace_get_received_packets()
	 */
	uint64_t received;

	/** The number of packets that have been dropped on an input trace
	 * due to lack of buffer space on the capturing device. This does not
	 * included errored packets which are dropped directly by the card.
	 *
	 * @note This field replaces trace_get_dropped_packets()
	 */
	uint64_t dropped;

	/** The number of received packets that have not been dropped. This
	 * includes filtered packets.
	 *
	 * This is equivalent to received-dropped.
	 *
	 * @note This may include a small number of buffered packets
	 *       not yet included in accepted.
	 */
        uint64_t captured;

        /** The number of packets (or aggregated records) that have been
         *  lost between the original capture device and the current input
         *  trace.
         *
         *  @note Only relevant for input formats that use a network to
         *  transfer live captured packets from one host to another (e.g.
         *  nDAG).
         */
        uint64_t missing;

	/** The number of packets that have been discarded by the network card
	 * because they are invalid. That includes FCS mismatches, incorrect
	 * packet lengths etc.
	 */
	uint64_t errors;
} libtrace_stat_t;

ct_assert(offsetof(libtrace_stat_t, accepted) == 8);

/** Sets an output config option
 *
 * @param libtrace	The output trace object to apply the option to
 * @param option	The option to set
 * @param value		The value to set the option to
 * @return -1 if option configuration failed, 0 otherwise
 * This should be called after trace_create_output, and before 
 * trace_start_output
 */
DLLEXPORT int trace_config_output(libtrace_out_t *libtrace, 
		trace_option_output_t option,
		void *value
		);

/** Close an input trace, freeing up any resources it may have been using
 *
 * @param trace 	The input trace to be destroyed
 *
 */
DLLEXPORT void trace_destroy(libtrace_t *trace);

/** Close a dummy trace file, freeing up any resources it may have been using
 * @param trace		The dummy trace to be destroyed
 */
DLLEXPORT void trace_destroy_dead(libtrace_t *trace);

/** Close an output trace, freeing up any resources it may have been using
 * @param trace		The output trace to be destroyed
 */
DLLEXPORT void trace_destroy_output(libtrace_out_t *trace);

/** Flush an output trace, forcing any buffered packets to be written
 * @param libtrace      The output trace to be flushed
 * @return 0 on success, otherwise an error occurred
 *
 * @note This flushes buffers immediately, but does not block until all
 *       packets are transmitted on the wire or synchronised to disk.
 */
DLLEXPORT int trace_flush_output(libtrace_out_t *libtrace);

/** Check (and clear) the current error state of an input trace
 * @param trace		The input trace to check the error state on
 * @return The current error status and message
 *
 * This reads and returns the current error state and sets the current error 
 * to "no error".
 */
DLLEXPORT libtrace_err_t trace_get_err(libtrace_t *trace);

/** Function to get a generic string representation of an error number
 * @param errnum    The error number to get the string representation of
 * @return The string representation of error number
 */
DLLEXPORT const char *trace_get_errstr(int errnum);

/** Indicate if there has been an error on an input trace
 * @param trace		The input trace to check the error state on
 * @return true if an error has occurred, false otherwise
 *
 * @note This does not clear the error status, and only returns true or false.
 */
DLLEXPORT bool trace_is_err(libtrace_t *trace);

/** Outputs the error message for an input trace to stderr and clear the error 
 * status.
 * @param trace		The input trace with the error to output
 * @param msg		The message to prepend to the error
 *
 * This function does clear the error status.
 */
DLLEXPORT void trace_perror(libtrace_t *trace, const char *msg,...) PRINTF(2,3);

/** Checks (and clears) the current error state for an output trace
 * @param trace		The output trace to check the error state on
 * @return The current error status and message
 * 
 * This reads and returns the current error state and sets the current error 
 * to "no error".
 */
DLLEXPORT libtrace_err_t trace_get_err_output(libtrace_out_t *trace);

/** Indicates if there is an error on an output trace
 * @param trace		The output trace to check the error state on
 * @return true if an error has occurred, false otherwise.
 *
 * This does not clear the error status, and only returns true or false.
 */
DLLEXPORT bool trace_is_err_output(libtrace_out_t *trace);

/** Outputs the error message for an output trace to stderr and clear the error
 * status.
 * @param trace		The output trace with the error to output
 * @param msg		The message to prepend to the error
 * This function does clear the error status.
 */
DLLEXPORT void trace_perror_output(libtrace_out_t *trace, const char *msg,...)
	PRINTF(2,3);

/** Returns the number of packets observed on an input trace. 
 * Includes the number of packets counted as early as possible, before
 * filtering, and includes dropped packets.
 *
 * @param trace		The input trace to examine
 * @returns The number of packets seen at the capture point before filtering.
 *
 * If the number is not known, this function will return UINT64_MAX
 *
 * @deprecated This function is deprecated: Use trace_get_statistics(), this
 *             allows all statistic counters to be read in an atomic manner.
 */
DLLEXPORT DEPRECATED
uint64_t trace_get_received_packets(libtrace_t *trace);

/** Returns the number of packets that were captured, but discarded for not
 * matching a provided filter. 
 *
 * @param trace		The input trace to examine
 * @returns The number of packets that were successfully captured, but filtered
 *
 * If the number is not known, this function will return UINT64_MAX
 *
 * @deprecated This function is deprecated: Use trace_get_statistics(), this
 *             allows all statistic counters to be read in an atomic manner.
 */
DLLEXPORT DEPRECATED
uint64_t trace_get_filtered_packets(libtrace_t *trace);

/** Returns the number of packets that have been dropped on an input trace due 
 * to lack of buffer space on the capturing device.
 *
 * @param trace		The input trace to examine
 * @returns The number of packets captured, but dropped due to buffer overruns
 *
 * If the number is not known, this function will return UINT64_MAX
 *
 * @deprecated This function is deprecated: Use trace_get_statistics(), this
 *             allows all statistic counters to be read in an atomic manner.
 */
DLLEXPORT DEPRECATED
uint64_t trace_get_dropped_packets(libtrace_t *trace);

/** Returns the number of packets that have been read from the input trace using
 * trace_read_packet().
 *
 * @param trace		The input trace to examine
 * @returns The number of packets that have been read by the libtrace user.
 *
 * If the number is not known, this function will return UINT64_MAX
 *
 * @deprecated This function is deprecated: Use trace_get_statistics(), this
 *             allows all statistic counters to be read in an atomic manner.
 */
DLLEXPORT DEPRECATED
uint64_t trace_get_accepted_packets(libtrace_t *trace);

/**
 * Returns statistic counters for a trace, for a parallel trace this is a
 * combined total.
 * Where possible these are retrieved atomically, however this behaviour depends
 * on the underlying trace format.
 *
 * @param trace The input trace to examine.
 * @param stats Optional, Filled upon return with statistics about the trace,
 *              check the flags included to see if a given statistic is valid.
 *              If NULL a statistic structure owned by libtrace is returned, this
 *              should not be free'd and will become invalid if the trace is
 *              destroyed.
 *
 * @return A pointer to the statistics structure.
 * @note Use trace_create_stat() to create the stats object, this way future
 *       versions of libtrace can add to the structure without breaking existing
 *       code.
 */
DLLEXPORT
libtrace_stat_t *trace_get_statistics(libtrace_t *trace, libtrace_stat_t *stats);


/**
 * Returns statistic counters for a single thread of a trace.
 * Where possible these are retrieved atomically, however this behaviour depends
 * on the underlying trace format.
 *
 * @param trace The input trace to examine.
 * @param t An optional thread to received stats for or NULL to retrieve stats
 *          for the current thread
 * @param stats Filled upon return with statistics about the trace, check the
 *              flags included to see if a given statistic is valid.
 *
 * @note Use trace_create_stat() to create the stats object, this way future
 *       versions of libtrace can add to the structure without breaking existing
 *       code.
 */
DLLEXPORT
void trace_get_thread_statistics(libtrace_t *trace, libtrace_thread_t *t,
                                 libtrace_stat_t *stats);

/**
 * Creates and returns a zeroed libtrace_stat_t structure.
 *
 * This allows us to add extra fields increasing the size of the structure
 * without breaking existing libtrace applications.
 *
 * This structure should be free'd using free().
 *
 * @return A valid pointer to a libtrace_stat_t struct otherwise NULL if
 *         memory was not available.
 */
DLLEXPORT libtrace_stat_t* trace_create_statistics(void);

/**
 * Clear all fields of given statistic.
 * This api doesn't verify the magic field unlike other stat apis.
 *
 * @param s The statistic structure to clear
 */
DLLEXPORT
void trace_clear_statistics(libtrace_stat_t *s);

/**
 * Performs the operation c=a-b accounting for valid fields.
 * c is allowed to be a or b.
 *
 * @param a The minuend
 * @param b The subtrahend
 * @param c The resulting difference
 */
DLLEXPORT
void trace_subtract_statistics(const libtrace_stat_t *a,
                               const libtrace_stat_t *b, libtrace_stat_t *c);

/**
 * Performs operation c=a+b accounting for valid fields.
 * c is allowed to be a or b.
 *
 * @param a The first operand
 * @param b The second operand
 * @param c The result
 */
DLLEXPORT
void trace_add_statistics(const libtrace_stat_t *a,
                          const libtrace_stat_t *b, libtrace_stat_t *c);

/**
 * Prints all valid stats to a file stream, (which could be stdout/err).
 * By default the format "name: value" is used.
 *
 * @param s The statistic structure to print
 * @param f The output file stream
 * @param format An optional format string such as the default ("%s: %"PRIu64"\n")
 *               This is passed to fprintf and called with two arguments
 *               first a char* (%s) and second a uint64_t (%PRIu64).
 *
 * @return -1 if an error occurs when writing to the file stream, check errno.
 *         Otherwise 0.
 */
DLLEXPORT
int trace_print_statistics(const libtrace_stat_t *s, FILE *f,
                           const char *format);


/*@}*/

/** @name Reading / Writing packets
 * These members deal with creating, reading and writing packets
 *
 * @{
 */

/** Create a new packet object
 *
 * @return A pointer to an initialised libtrace_packet_t object, or NULL if
 * libtrace is unable to allocate space for a new packet.
 */
DLLEXPORT libtrace_packet_t *trace_create_packet(void);

/** Copy a packet object
 * @param packet	The source packet to copy
 * @return A new packet which has the same content as the source packet
 *
 * @note This always involves a copy, which can be slow.  Use of this 
 * function should be avoided where possible.
 * 
 * @par The reason you would want to use this function is that a zero-copied
 * packet from a device will be stored using memory owned by the device which
 * may be a limited resource. Copying the packet will ensure that the packet
 * is now stored in memory owned and managed by libtrace.
 */
DLLEXPORT libtrace_packet_t *trace_copy_packet(const libtrace_packet_t *packet);

/** Destroy a packet object
 * @param packet 	The packet to be destroyed
 *
 */
DLLEXPORT void trace_destroy_packet(libtrace_packet_t *packet);

/** Read the next packet from an input trace 
 *
 * @param trace 	The libtrace opaque pointer for the input trace
 * @param packet  	The packet opaque pointer
 * @return 0 on EOF, negative value on error, number of bytes read when successful.
 *
 * @note The number of bytes read is usually (but not always) the same as
 * trace_get_framing_length()+trace_get_capture_length() depending on the
 * trace format.
 *
 * @note The trace must have been started with trace_start before calling
 * this function
 *
 * @note When reading from a live capture, this function will block until a
 * packet is observed on the capture interface. The libtrace event API 
 * (e.g. trace_event()) should be used if non-blocking operation is required.
 */
DLLEXPORT int trace_read_packet(libtrace_t *trace, libtrace_packet_t *packet);

/** Converts the data provided in buffer into a valid libtrace packet
 *
 * @param trace         An input trace of the same format as the "packet" 
 *                      contained in the buffer
 * @param packet        The libtrace packet to prepare
 * @param buffer        A buffer containing the packet data, including the
 *                      capture format header
 * @param rt_type       The RT type for the packet that is being prepared
 * @param flags         Used to specify options for the preparation function,
 *                      e.g. who owns the packet buffer
 *
 * @return -1 if an error occurs, 0 otherwise 
 *
 * Packet preparation is a tricky concept - the idea is to take the data
 * pointed to by 'buffer' and treat it as a packet record of the same capture
 * format as that used by the input trace. The provided libtrace packet then
 * has its internal pointers and values set to describe the packet record in
 * the buffer. 
 *
 * The primary use of this function is to allow the RT packet reader to 
 * easily and safely convert packets from the RT format back into the format
 * that they were originally captured with., essentially removing the RT
 * encapsulation.
 *
 * This function is now available via the exported API, as it can have some
 * uses outside of internal libtrace contexts. However, we strongly advise
 * that you avoid using this function unless you really know what you are
 * doing.
 */
DLLEXPORT int trace_prepare_packet(libtrace_t *trace, libtrace_packet_t *packet,
                void *buffer, libtrace_rt_types_t rt_type, uint32_t flags);

/** Flags for prepare_packet functions */
enum {
        /** The buffer memory has been allocated by libtrace and should be
         * freed when the packet is destroyed. */
        TRACE_PREP_OWN_BUFFER           =1,

        /** The buffer memory is externally-owned and must not be freed by 
         * libtrace when the packet is destroyed. */
        TRACE_PREP_DO_NOT_OWN_BUFFER    =0
};


/** Event types 
 * see \ref libtrace_eventobj_t and \ref trace_event
 */
typedef enum {
	TRACE_EVENT_IOWAIT,	/**< Wait on the given file descriptor */
	TRACE_EVENT_SLEEP,	/**< Sleep for the given amount of time */
	TRACE_EVENT_PACKET,	/**< Packet has been read from input trace */
	TRACE_EVENT_TERMINATE	/**< End of input trace */
} libtrace_event_t;

/** Structure returned by libtrace_event explaining what the current event is */
typedef struct libtrace_eventobj_t {
	libtrace_event_t type; /**< Event type (iowait,sleep,packet) */
	
	/** If the event is IOWAIT, the file descriptor to wait on */
	int fd;		       
	/** If the event is SLEEP, the amount of time to sleep for in seconds */
	double seconds;	       
	/** If the event is PACKET, the value returned by trace_read_packet() */
	int size; 
} libtrace_eventobj_t;

/** Processes the next libtrace event from an input trace.
 * @param trace The libtrace opaque pointer for the input trace
 * @param packet The libtrace_packet opaque pointer to use for reading packets
 * @return A libtrace_event struct containing the event type and details of the event.
 *
 * Type can be:
 *  TRACE_EVENT_IOWAIT	Waiting on I/O on a file descriptor
 *  TRACE_EVENT_SLEEP	Wait a specified amount of time for the next event
 *  TRACE_EVENT_PACKET	Packet was read from the trace
 *  TRACE_EVENT_TERMINATE Trace terminated (perhaps with an error condition)
 */
DLLEXPORT libtrace_eventobj_t trace_event(libtrace_t *trace,
		libtrace_packet_t *packet);


/** Write one packet out to the output trace
 *
 * @param trace		The libtrace_out opaque pointer for the output trace
 * @param packet	The packet opaque pointer of the packet to be written
 * @return The number of bytes written out, if zero or negative then an error has occured.
 */
DLLEXPORT int trace_write_packet(libtrace_out_t *trace, libtrace_packet_t *packet);

/** Gets the capture format for a given packet.
 * @param packet	The packet to get the capture format for.
 * @return The capture format of the packet
 *
 * @note Due to ability to convert packets between formats relatively easily
 * in Libtrace, the format of the packet right now may not be the format that
 * the packet was originally captured with.
 */
DLLEXPORT 
enum base_format_t trace_get_format(struct libtrace_packet_t *packet);

/** Construct a libtrace packet from a buffer containing the packet payload.
 * @param[in,out] packet	Libtrace Packet object to update with the new 
 * 				data.
 * @param linktype		The linktype of the packet data.
 * @param[in] data		The packet data (including linklayer).
 * @param len			Length of packet data provided in the buffer.
 *
 * @note The constructed packet will be in the PCAP format.
 *
 * @note To be useful, the provided buffer must start with the layer 2 header
 * (or a metadata header, if desired).
 */
DLLEXPORT
void trace_construct_packet(libtrace_packet_t *packet,
		libtrace_linktype_t linktype, const void *data, uint16_t len);

/*@}*/

/** @name Protocol decodes
 * These functions locate and return a pointer to various headers inside a
 * packet
 * 
 * A packet is divided up into several "layers.":
 *
 * @li Framing header -- This is the header provided by the capture format 
 * itself rather than anything that was sent over the network. This provides
 * basic details about the packet record including capture lengths, wire 
 * lengths, timestamps, direction information and any other metadata that is 
 * part of the capture format.  
 * 
 * @li Metadata header (optional) -- A header containing metadata about a 
 * packet that was captured, but the metadata was not transmitted over the 
 * wire.  Some examples include RadioTap and Linux_sll headers.  This can be 
 * retrieved by trace_get_packet_meta(), or skipped using 
 * trace_get_payload_from_meta(). There may be multiple "metadata" headers on 
 * a packet.
 *
 * @li Layer 2/Link layer/Datalink header -- This can be retrieved by 
 * trace_get_layer2(), or skipped using trace_get_payload_from_layer2().
 *
 * @li Layer 3/IP/IPv6 -- This can be retrieved by trace_get_layer3().  As a 
 * convenience trace_get_ip()/trace_get_ip6() can be used to find an IPv4/IPv6 
 * header.
 *
 * @li Layer 5/transport -- These are protocols carried in IPv4/IPv6 frames. 
 * These can be retrieved using trace_get_transport().
 * 
 * @{
 */


/** Gets a pointer to the first byte of the packet as it was captured and
 * returns its corresponding linktype and capture length.
 *
 * Use this function instead of the deprecated trace_get_link().
 *
 * @param packet The packet to get the buffer from
 * @param[out] linktype The linktype of the returned pointer
 * @param[out] remaining The capture length (the number of captured bytes from
 * the returned pointer)
 * @return A pointer to the first byte of the packet
 */
DLLEXPORT void *trace_get_packet_buffer(const libtrace_packet_t *packet,
                libtrace_linktype_t *linktype, uint32_t *remaining);

/** Get a pointer to the link layer for a given packet
 * @param packet  	The packet to get the link layer for
 *
 * @return A pointer to the link layer, or NULL if there is no link layer
 *
 * @deprecated This function is deprecated: Use trace_get_packet_buffer() or
 * one of the trace_get_layer*() functions instead.
 * @note You should call trace_get_link_type to find out what type of link
 * layer has been returned to you.
 */
DLLEXPORT SIMPLE_FUNCTION DEPRECATED
void *trace_get_link(const libtrace_packet_t *packet);

/** Strips layer 2.5 headers from a given packet.
 * @param packet        The packet to strip headers from.
 *
 * @return The packet with the requested headers removed (if they were
 * present).
 *
 * This function is intended for removing those pesky layer 2.5 headers
 * that are not supported by other packet analysis applications, e.g. VLAN
 * and MPLS headers. If successful, the resulting packet will be a simple
 * Ethernet-IP-Transport packet that just about anything should be able to
 * parse without difficulty.
 *
 * If this function encounters a layer 2 or 2.5 header that it does not
 * support, stripping will cease and the packet returning will be stripped
 * up to but not including the unsupported header.
 *
 * New in libtrace 4.0.0
 *
 * @note This function only supports stripping headers from Ethernet packets
 * for now. Passing in packets of other link types will simply result in
 * the original packet being returned unmodified.
 *
 */
DLLEXPORT libtrace_packet_t *trace_strip_packet(libtrace_packet_t *packet);

/** Get a pointer to the IPv4 header (if any) for a given packet
 * @param packet  	The packet to get the IPv4 header for
 *
 * @return A pointer to the IPv4 header, or NULL if there is no IPv4 header
 *
 * If a partial IP header is present, i.e. the packet has been truncated before
 * the end of the IP header, this function will return NULL.
 *
 * You should consider using \ref trace_get_layer3 instead of this function.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_ip_t *trace_get_ip(libtrace_packet_t *packet);

/** get a pointer to the IPv6 header (if any)
 * @param packet  	The packet to get the IPv6 header for
 *
 * @return A pointer to the IPv6 header, or NULL if there is no IPv6 header
 *
 * If a partial IPv6 header is present, i.e. the packet has been truncated
 * before the end of the IP header, this function will return NULL.
 *
 * You should consider using \ref trace_get_layer3 instead of this function.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_ip6_t *trace_get_ip6(libtrace_packet_t *packet);

/** Return a pointer to the first metadata header in a packet, if present.
 *
 * This function takes a pointer to a libtrace packet and if any metadata
 * headers exist, returns a pointer to the first one, along with its
 * corresponding linktype. 
 *
 * If no metadata headers exist in the packet, NULL is returned.
 *
 * A metadata header is a header that was prepended by the capturing device,
 * such as a Linux SLL header, or a Radiotap wireless monitoring header.
 * Subsequent metadata headers may be accessed with the
 * trace_get_payload_from_meta(...) function. 
 *
 * @param packet The libtrace packet
 * @param[out] linktype The linktype of the returned metadata header
 * @param[out] remaining The number of bytes captured after the returned
 * pointer.
 * @return A pointer to the first metadata header, or NULL if there are no
 * metadata headers present.
 *
 * remaining may be NULL, however linktype must be provided.
 */
DLLEXPORT void *trace_get_packet_meta(const libtrace_packet_t *packet,
                libtrace_linktype_t *linktype,
                uint32_t *remaining);

/** Returns the payload of a metadata header.
 * 
 * This function takes a pointer to the start of a metadata header (either
 * obtained via trace_get_packet_meta(...) or by a previous call to
 * trace_get_payload_from_meta(...)) along with its corresponding linktype and
 * returns the payload, i.e. the next header. It will also update the linktype
 * parameter to indicate the type of payload.
 *  
 * If the linktype indicates that the header passed in is not a metadata
 * header, the function returns NULL to indicate this. The linktype remains
 * unchanged in this case.
 *
 * This function allows the user to iterate through metadata headers which are
 * sometimes present before the actual packet as it was received on the wire.
 * Examples of metadata headers include the Linux SLL header and the Radiotap
 * wireless monitoring header.
 *
 * If the metadata header passed into this function is truncated, this 
 * function will return NULL, and remaining will be set to 0.
 *
 * If there are 0 bytes of payload following the provided metadata header, the 
 * function will return a pointer to where the header would otherwise be and 
 * remaining will be 0.
 *
 * Therefore, be sure to check the value of remaining after calling this
 * function!
 *
 * @param[in] meta A pointer to a metadata header
 * @param[in,out] linktype The linktype of meta (updated to indicate the
 * linktype of the returned header if applicable).
 * @param[in,out] remaining The number of bytes after the meta pointer.
 * @return A pointer to the payload of the metadata header. If meta is not a
 * pointer to a metadata header, NULL is returned and linktype remains
 * unchanged.
 *
 * All parameters are mandatory. 
 */
DLLEXPORT void *trace_get_payload_from_meta(const void *meta,
                libtrace_linktype_t *linktype,
                uint32_t *remaining);


/** Get a pointer to the layer 2 header. Generally this is the first byte of the
 * packet as it was seen on the wire.
 * 
 * This function takes a libtrace packet and skips over any metadata headers if
 * present (such as Linux SLL or Radiotap) and returns a pointer to the first
 * byte of the packet that was actually received by the network interface.
 *
 * @param packet The libtrace packet to find the layer 2 header for
 * @param[out] linktype The linktype of the returned layer 2 header
 * @param[out] remaining The number of bytes left in the packet after the
 * returned pointer.
 * @return A pointer to the first byte of the packet as it was seen on the
 * wire. If no layer 2 header is present, this function will return NULL.
 *
 * remaining may be NULL, otherwise it will be filled in by the function.
 */
DLLEXPORT void *trace_get_layer2(const libtrace_packet_t *packet,
                libtrace_linktype_t *linktype,
                uint32_t *remaining);

/** Gets a pointer to the next header following a layer 2 header
 *
 * @param l2            	The pointer to the current layer 2 header
 * @param linktype		The type of the layer 2 header
 * @param[out] ethertype 	An optional output variable of the ethernet type of the new header
 * @param[in,out] remaining 	Updated with the number of captured bytes 
				remaining
 *
 * @return A pointer to the header following the provided layer 2 header, or 
 * NULL if no subsequent header is present.
 *
 * Remaining must point to the number of bytes captured from the layer 2 header
 * and beyond.  It will be decremented by the number of bytes skipped to find
 * the payload.
 *
 * If the layer 2 header is complete but there are zero bytes of payload after 
 * the end of the header, a pointer to where the payload would be is returned 
 * and remaining will be set to 0.  If the layer 2 header is incomplete 
 * (truncated), then NULL is returned and remaining will be set to 0. 
 * Therefore, it is very important to check the value of remaining after
 * calling this function. 
 *
 */
DLLEXPORT void *trace_get_payload_from_layer2(void *l2,
		libtrace_linktype_t linktype,
		uint16_t *ethertype,
		uint32_t *remaining);


/** Get a pointer to the layer 3 (e.g. IP) header.
 * @param packet  The libtrace packet to find the layer 3 header for
 * @param[out] ethertype The ethertype of the layer 3 header
 * @param[out] remaining The amount of captured data remaining in the packet starting from the returned pointer, i.e. including the layer 3 header.
 *
 * @return A pointer to the layer 3 header. If no layer 3 header is present in
 * the packet, NULL is returned. If the layer 3 header is truncated, a valid 
 * pointer will still be returned so be sure to check the value of remaining
 * before attempting to process the returned header.
 *
 * remaining may be NULL, otherwise it will be set to the number of captured
 * bytes after the pointer returned.
 */
DLLEXPORT 
void *trace_get_layer3(const libtrace_packet_t *packet,
		uint16_t *ethertype, uint32_t *remaining);

/** Calculates the expected IP checksum for a packet.
 * @param packet	The libtrace packet to calculate the checksum for
 * @param[out] csum	The checksum that is calculated by this function. This
 * 			may not be NULL.
 * 
 * @return A pointer to the original checksum field within the IP
 * header. If the checksum field is not present in the packet, NULL is returned.
 *
 * @note The return value points to the checksum that exists within the current
 * packet. The value in csum is the value that the checksum should be, given
 * the current packet contents.  
 *
 * @note This function involves the use of a memcpy, so be careful about
 * calling it excessively if performance is a concern for you.
 * 
 * New in libtrace 3.0.17
 */
DLLEXPORT uint16_t *trace_checksum_layer3(libtrace_packet_t *packet, 
		uint16_t *csum);

/** Calculates the expected checksum for the transport header in a packet.
 * @param packet	The libtrace packet to calculate the checksum for
 * @param[out] csum	The checksum that is calculated by this function. This
 * 			may not be NULL.
 * 
 * @return A pointer to the original checksum field within the transport 
 * header. If the checksum field is not present in the packet, NULL is returned.
 *
 * @note The return value points to the checksum that exists within the current
 * packet. The value in csum is the value that the checksum should be, given
 * the current packet contents.  
 *
 * @note This function involves the use of a memcpy, so be careful about
 * calling it excessively if performance is a concern for you.
 * 
 * @note Because transport checksums are calculated across the entire payload,
 * truncated packets will result in NULL being returned.
 *
 * This function will determine the appropriate checksum for whatever transport
 * layer header is present in the provided packet. At this stage, this only
 * currently works for TCP, UDP and ICMP packets.
 *
 * Be wary of TCP checksum offloading if you are examining the checksum of
 * packets captured on the same host that generated them!
 *
 * New in libtrace 3.0.17
 */
DLLEXPORT uint16_t *trace_checksum_transport(libtrace_packet_t *packet,
                uint16_t *csum);

/** Calculates the fragment offset in bytes for an IP packet
 * @param packet        The libtrace packet to calculate the offset for
 * @param[out] more     A boolean flag to indicate whether there are more
 *                      fragments after the current packet.
 * @return The fragment offset for the packet in bytes. If the packet is not
 * an IP packet or the fragment offset is not present in packet, the return
 * value will be 0.
 *
 * @note The value returned is in bytes, not 8-octet units as it is stored
 * in the fragment offset field in the headers. In other words, libtrace
 * automatically does the multiplication for you.
 *
 * The value passed in for 'more' does not matter; it will be overwritten
 * with the value of the More Fragments flag from the IP header.
 *
 * New in libtrace 3.0.20
 */
DLLEXPORT uint16_t trace_get_fragment_offset(const libtrace_packet_t *packet,
                uint8_t *more); 

/** Gets a pointer to the transport layer header (if any)
 * @param packet   The libtrace packet to find the transport header for
 * @param[out] proto	The protocol present at the transport layer.
 * @param[out] remaining The amount of captured data remaining in the packet 
 * starting from the returned pointer, i.e. including the transport header.
 *
 * @return A pointer to the transport layer header. If no transport header is
 * present in the packet, NULL is returned. If the transport header is 
 * truncated, a valid pointer will still be returned so be sure to check the
 * value of remaining before attempting to process the returned header.
 *
 * remaining may be NULL, otherwise it will be set to the number of captured
 * bytes after the returned pointer.
 *
 * @note proto may be NULL if proto is unneeded.
 */
DLLEXPORT void *trace_get_transport(const libtrace_packet_t *packet, 
		uint8_t *proto, uint32_t *remaining);

/** Gets a pointer to the payload following an IPv4 header
 * @param ip            The IPv4 Header
 * @param[out] proto	The protocol of the header following the IPv4 header
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the transport layer header, or NULL if no subsequent 
 * header is present.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the IPv4 header (including the
 * IPv4 header itself).
 *
 * remaining will be decremented by the size of the IPv4 header (including any 
 * options). If the IPv4 header is complete but there are zero bytes of payload
 * after the IPv4 header, a pointer to where the payload would be is returned 
 * and remaining will be set to 0.  If the IPv4 header is incomplete, NULL will
 * be returned and remaining will be set to 0. Therefore, it is very important
 * to check the value of remaining after calling this function.
 *
 * proto may be NULL, in which case it won't be updated.
 *
 * @note This is similar to trace_get_transport_from_ip in libtrace2
 */
DLLEXPORT void *trace_get_payload_from_ip(libtrace_ip_t *ip, uint8_t *proto,
		uint32_t *remaining);

/** Gets a pointer to the payload following an IPv6 header
 * @param ipptr         The IPv6 Header
 * @param[out] proto	The protocol of the header following the IPv6 header
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the transport layer header, or NULL if no subsequent 
 * header is present.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the IPv6 header (including the
 * IPv6 header itself).
 *
 * remaining will be decremented by the size of the IPv6 header (including any 
 * options). If the IPv6 header is complete but there are zero bytes of payload
 * after the IPv6 header, a pointer to where the payload would be is returned 
 * and remaining will be set to 0.  If the IPv6 header is incomplete, NULL will
 * be returned and remaining will be set to 0. Therefore, it is very important
 * to check the value of remaining after calling this function.
 *
 * proto may be NULL, in which case it won't be updated.
 *
 */
DLLEXPORT void *trace_get_payload_from_ip6(libtrace_ip6_t *ipptr,
                uint8_t *proto, uint32_t *remaining);

/** Gets a pointer to the payload following a link header
 * @param linkptr       A pointer to the link layer header
 * @param linktype	The linktype of the link header being examined
 * @param[out] type	An output variable for the ethernet type
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the header following the link header, or NULL if no
 * subsequent header is present.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the link header (including the
 * link header itself). remaining will be updated to contain the number of 
 * bytes remaining after the link header has been skipped.
 *
 * @deprecated This function is deprecated: you should be using 
 * trace_get_payload_from_layer2() or trace_get_payload_from_meta() instead.
 *
 */
DLLEXPORT void *trace_get_payload_from_link(void *linkptr,
		libtrace_linktype_t linktype, 
		uint16_t *type, uint32_t *remaining);

/** Gets a pointer to the payload following an 802.1q (VLAN) header.
 * @param vlan      A pointer to the VLAN header
 * @param[out] type  The ethernet type, replaced with the VLAN ether type
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the header beyond the VLAN header, if one is present.
 * Otherwise, returns NULL.  
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the VLAN header (including the
 * VLAN header itself). remaining will be updated to contain the number of 
 * bytes remaining after the VLAN header has been skipped.
 *
 * If the VLAN header is complete but there are zero bytes of payload after 
 * the VLAN header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the VLAN header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 * type will be set to the ethertype of the VLAN payload. This parameter is not
 * mandatory, but is highly recommended.
 *
 */
DLLEXPORT void *trace_get_payload_from_vlan(
                void *vlan, uint16_t *type, uint32_t *remaining);

/** Get the outermost VLAN ID from a packet.
 * @param packet		A pointer to the packet
 * @param[out] vlanptr		A pointer to the VLAN header
 * @param[out] remaining	Updated with the number of captured bytes remaining
 *
 * @return The outermost VLAN id if found or VLAN_NOT_FOUND
 *
 * vlanptr will be set to the start of the VLAN header found (or NULL if no
 * VLAN tags are present).
 *
 * remaining will be set to the number of captured bytes in the packet,
 * starting from the returned VLAN header.
 */
DLLEXPORT uint16_t trace_get_outermost_vlan(
	libtrace_packet_t *packet, uint8_t **vlanptr, uint32_t *remaining);

/** Get all layer2 headers from a packet.
 * @param packet	A pointer to the packet
 *
 * @return A libtrace_layer2_headers_t structure containing all found layer2
 * headers (or NULL if no layer2 headers are found). This structure must be
 * destroyed with trace_destroy_layer2_headers().
 */
DLLEXPORT libtrace_layer2_headers_t *trace_get_layer2_headers(libtrace_packet_t *packet);

/** Destroys a libtrace_layer2_headers_t structure.
 * @param headers	A pointer to the libtrace_layer2_headers_t structure
 *
 * @returns 1 on successful deletion.
 */
DLLEXPORT int trace_destroy_layer2_headers(libtrace_layer2_headers_t *headers);

/** Get the outermost MPLS label from a packet.
 * @param packet		A pointer to the packet
 * @param[out] mplsptr		A pointer to the mpls header
 * @param[out] remaining	Updated with the number of captured bytes remaining
 *
 * @return The outmost MPLS label if found or MPLS_NOT_FOUND
 *
 * mplsptr will be set to the start of the MPLS header (or NULL if no
 * MPLS header is found)
 *
 * remaining will be set to the number of captured bytes in the packet,
 * starting from the MPLS header.
 */
DLLEXPORT uint32_t trace_get_outermost_mpls(
	libtrace_packet_t *packet, uint8_t **mplsptr, uint32_t *remaining);

/** Gets a pointer to the payload following an MPLS header.
 * @param mpls      A pointer to the MPLS header
 * @param[out] type  The ethernet type, replaced by the ether type of the
 * returned header - 0x0000 if an Ethernet header is returned
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the header beyond the MPLS label, if one is present. 
 * Will return NULL if there is not enough bytes remaining to skip past the 
 * MPLS label.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the MPLS header (including the
 * MPLS header itself). remaining will be updated to contain the number of 
 * bytes remaining after the MPLS header has been skipped.
 *
 * If the MPLS header is complete but there are zero bytes of payload after 
 * the MPLS header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the MPLS header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 * type will be set to the ethertype of the MPLS payload. This parameter is
 * mandatory - it may not be NULL.
 *
 * @note This function will only remove one MPLS label at a time - the type
 * will be set to 0x8847 if there is another MPLS label following the one
 * skipped by this function.
 *
 */
DLLEXPORT void *trace_get_payload_from_mpls(
                void *mpls, uint16_t *type, uint32_t *remaining);

/** Gets a pointer to the payload following a PPPoE header
 * @param pppoe      A pointer to the PPPoE header
 * @param[out] type  The ethernet type, replaced by the ether type of the
 * returned header - 0x0000 if an Ethernet header is returned
 * @param[in,out] remaining  Updated with the number of captured bytes remaining
 *
 * @return A pointer to the header beyond the PPPoE header. NOTE that this
 * function will also skip over the PPP header that will immediately follow
 * the PPPoE header. This function will return NULL if there are not enough
 * bytes remaining to skip past both the PPPoE and PPP headers.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the PPPoE header (including the
 * PPPoE header itself). remaining will be updated to contain the number of 
 * bytes remaining after the PPPoE and PPP headers have been removed.
 *
 * If the PPPoE and PPP headers are complete but there are zero bytes of 
 * payload after the PPP header, a pointer to where the payload would be is 
 * returned and remaining will be set to 0.  If the PPPoE or PPP header is 
 * incomplete, NULL will be returned and remaining will be set to 0. Therefore, 
 * it is important to check the value of remaining after calling this function.
 *
 * type will be set to the ether type of the PPP payload. This parameter is
 * mandatory - it may not be NULL.
 *
 */
DLLEXPORT void *trace_get_payload_from_pppoe(
		void *pppoe, uint16_t *type, uint32_t *remaining);

/** Gets a pointer to the payload following a TCP header
 * @param tcp           A pointer to the TCP header
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the TCP payload, or NULL if the TCP header is truncated.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the TCP header (including the
 * TCP header itself). remaining will be updated to contain the number of 
 * bytes remaining after the TCP header has been skipped.
 *
 * If the TCP header is complete but there are zero bytes of payload after 
 * the TCP header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the TCP header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 */
DLLEXPORT void *trace_get_payload_from_tcp(libtrace_tcp_t *tcp, 
		uint32_t *remaining);

/** Gets a pointer to the payload following a UDP header
 * @param udp           A pointer to the UDP header
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the UDP payload, or NULL if the UDP header is truncated.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the UDP header (including the
 * UDP header itself). remaining will be updated to contain the number of 
 * bytes remaining after the UDP header has been skipped.
 *
 * If the UDP header is complete but there are zero bytes of payload after 
 * the UDP header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the UDP header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 */
DLLEXPORT void *trace_get_payload_from_udp(libtrace_udp_t *udp, uint32_t *remaining);

/** Gets a pointer to the payload following a ICMP header
 * @param icmp           A pointer to the ICMP header
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the ICMP payload, or NULL if the ICMP header is 
 * truncated.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the ICMP header (including the
 * ICMP header itself). remaining will be updated to contain the number of 
 * bytes remaining after the ICMP header has been skipped.
 *
 * If the ICMP header is complete but there are zero bytes of payload after 
 * the ICMP header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the ICMP header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 * @note In the case of some ICMP messages, the payload may be the IP header
 * from the packet that triggered the ICMP message. 
 *
 */
DLLEXPORT void *trace_get_payload_from_icmp(libtrace_icmp_t *icmp, 
		uint32_t *remaining);

/** Gets a pointer to the payload following a ICMPv6 header
 * @param icmp           A pointer to the ICMPv6 header
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the ICMPv6 payload, or NULL if the ICMPv6 header is 
 * truncated.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the ICMPv6 header (including the
 * ICMP header itself). remaining will be updated to contain the number of 
 * bytes remaining after the ICMPv6 header has been skipped.
 *
 * If the ICMPv6 header is complete but there are zero bytes of payload after 
 * the header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the ICMPv6 header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 * @note In the case of some ICMPv6 messages, the payload may be the IP header
 * from the packet that triggered the ICMP message. 
 *
 */
DLLEXPORT void *trace_get_payload_from_icmp6(libtrace_icmp6_t *icmp, 
		uint32_t *remaining);

/** Gets a pointer to the payload following a GRE header
 * @param         gre       A pointer to the beginning of the GRE header.
 * @param[in,out] remaining Updated with the number of captured bytes remaining.
 *
 * @return A pointer to the GRE payload, or NULL if the GRE header is truncated.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the GRE header (including the
 * GRE header itself). remaining will be updated to contain the number of
 * bytes remaining after the GRE header has been skipped.
 *
 * If the GRE header is complete but there are zero bytes of payload after 
 * the header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the GRE header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 */
DLLEXPORT void *trace_get_payload_from_gre(libtrace_gre_t *gre,
                uint32_t *remaining);

/** Gets a pointer to the payload following a VXLAN header
 * @param         udp       A pointer to the beginning of the UDP header.
 * @param[in,out] remaining Updated with the number of captured bytes remaining.
 *
 * @return A pointer to the beginning of the VXLAN header, or NULL if the UDP
 * header is truncated, or this is not a VXLAN packet.
 *
 */
DLLEXPORT libtrace_vxlan_t *trace_get_vxlan_from_udp(libtrace_udp_t *udp,
                uint32_t *remaining);

/** Gets a pointer to the payload following a VXLAN header
 * @param         vxlan       A pointer to the beginning of the VXLAN header.
 * @param[in,out] remaining Updated with the number of captured bytes remaining.
 *
 * @return A pointer to the VXLAN payload, or NULL if the VXLAN header is
 * truncated.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the VXLAN header (including the
 * VXLAN header itself). remaining will be updated to contain the number of
 * bytes remaining after the VXLAN header has been skipped.
 *
 * If the VXLAN header is complete but there are zero bytes of payload after
 * the header, a pointer to where the payload would be is returned and
 * remaining will be set to 0.  If the VXLAN header is incomplete, NULL will be
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 */
DLLEXPORT void *trace_get_payload_from_vxlan(libtrace_vxlan_t *vxlan,
                uint32_t *remaining);

/** Get a pointer to the TCP header (if present)
 * @param packet  	The packet to get the TCP header from
 *
 * @return A pointer to the TCP header, or NULL if there is not a complete TCP
 * header present in the packet.
 *
 * This is a short-cut function enabling quick and easy access to the TCP
 * header if that is all you care about. However, we recommend the use of the
 * more generic trace_get_transport() function instead.
 *
 * @note Unlike trace_get_transport(), this function will return NULL if the
 * TCP header is incomplete or truncated.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_tcp_t *trace_get_tcp(libtrace_packet_t *packet);

/** Get a pointer to the TCP header following an IPv4 header (if present)
 * @param ip		The IP header to find the subsequent TCP header for
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the TCP header, or NULL if no TCP header is present in 
 * the packet.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the IP header (including the
 * IP header itself). remaining will be updated to contain the number of 
 * bytes remaining after the IP header has been skipped.
 *
 * If the IP header is complete but there are zero bytes of payload after 
 * the IP header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the IP header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 * @note This function is rather redundant now that the layer 3 header is
 * cached. There should be no performance advantage for the user to call this
 * function over just calling trace_get_transport().
 *
 * @note The last parameter has changed from libtrace2
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_tcp_t *trace_get_tcp_from_ip(libtrace_ip_t *ip, uint32_t *remaining);

/** Get a pointer to the UDP header (if present)
 * @param packet  	The packet to get the UDP header from
 *
 * @return A pointer to the UDP header, or NULL if there is not a complete UDP
 * header present in the packet.
 *
 * This is a short-cut function enabling quick and easy access to the UDP
 * header if that is all you care about. However, we recommend the use of the
 * more generic trace_get_transport() function instead.
 *
 * @note Unlike trace_get_transport(), this function will return NULL if the
 * UDP header is incomplete or truncated.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_udp_t *trace_get_udp(libtrace_packet_t *packet);

/** Get a pointer to the UDP header following an IPv4 header (if present)
 * @param ip		The IP header to find the subsequent UDP header for
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the UDP header, or NULL if no UDP header is present in 
 * the packet.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the IP header (including the
 * IP header itself). remaining will be updated to contain the number of 
 * bytes remaining after the IP header has been skipped.
 *
 * If the IP header is complete but there are zero bytes of payload after 
 * the IP header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the IP header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 * @note This function is rather redundant now that the layer 3 header is
 * cached. There should be no performance advantage for the user to call this
 * function over just calling trace_get_transport().
 *
 * @note The last parameter has changed from libtrace2
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_udp_t *trace_get_udp_from_ip(libtrace_ip_t *ip,uint32_t *remaining);

/** Get a pointer to the ICMP header (if present)
 * @param packet  	The packet to get the ICMP header from
 *
 * @return A pointer to the ICMP header, or NULL if there is not a complete 
 * ICMP header present in the packet.
 *
 * This is a short-cut function enabling quick and easy access to the ICMP
 * header if that is all you care about. However, we recommend the use of the
 * more generic trace_get_transport() function instead.
 *
 * @note Unlike trace_get_transport(), this function will return NULL if the
 * ICMP header is incomplete or truncated.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_icmp_t *trace_get_icmp(libtrace_packet_t *packet);

/** Get a pointer to the ICMPv6 header (if present)
 * @param packet  	The packet to get the ICMPv6 header from
 *
 * @return A pointer to the ICMPv6 header, or NULL if there is not a complete 
 * ICMP header present in the packet.
 *
 * This is a short-cut function enabling quick and easy access to the ICMPv6
 * header if that is all you care about. However, we recommend the use of the
 * more generic trace_get_transport() function instead.
 *
 * @note Unlike trace_get_transport(), this function will return NULL if the
 * ICMPv6 header is incomplete or truncated.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_icmp6_t *trace_get_icmp6(libtrace_packet_t *packet);

/** Get a pointer to the ICMP header following an IPv4 header (if present)
 * @param ip		The IP header to find the subsequent ICMP header for
 * @param[in,out] remaining Updated with the number of captured bytes remaining
 *
 * @return A pointer to the ICMP header, or NULL if no UDP header is present in 
 * the packet.
 *
 * When calling this function, remaining must contain the number of captured
 * bytes remaining in the packet starting from the IP header (including the
 * IP header itself). remaining will be updated to contain the number of 
 * bytes remaining after the IP header has been skipped.
 *
 * If the IP header is complete but there are zero bytes of payload after 
 * the IP header, a pointer to where the payload would be is returned and 
 * remaining will be set to 0.  If the IP header is incomplete, NULL will be 
 * returned and remaining will be set to 0. Therefore, it is important to check
 * the value of remaining after calling this function.
 *
 * @note This function is rather redundant now that the layer 3 header is
 * cached. There should be no performance advantage for the user to call this
 * function over just calling trace_get_transport().
 *
 * @note The last parameter has changed from libtrace2
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_icmp_t *trace_get_icmp_from_ip(libtrace_ip_t *ip,uint32_t *remaining);

/** Get a pointer to the OSPF header (if present)
 * @param packet	The packet to get the OSPF header from
 * @param[out] version	The OSPF version number
 * @param[out] remaining	Updated with the number of captured bytes remaining
 * @return A pointer to the start of the OSPF header or NULL if there is no 
 * complete OSPF header present in the packet
 *
 * This is a short-cut function enabling quick and easy access to the OSPF
 * header. If you only care about the OSPF header, this function may be useful
 * but we otherwise recommend the use of the more generic trace_get_transport()
 * function instead.
 *
 * Upon return, 'version' is updated to contain the OSPF version number for the
 * packet so that the returned pointer may be cast to the correct type.
 * The version parameter MUST contain a valid pointer; it MUST NOT be NULL.
 *
 * 'remaining' is also set to contain the number of captured bytes remaining
 * starting from the pointer returned by this function. 
 *
 * @note Unlike trace_get_transport(), this function will return NULL if the
 * OSPF header is incomplete or truncated.
 */
DLLEXPORT SIMPLE_FUNCTION
void *trace_get_ospf_header(libtrace_packet_t *packet, uint8_t *version,
		uint32_t *remaining);

/** Get a pointer to the contents of the OSPF packet *after* the OSPF header
 * @param header	The OSPF header to get the OSPF contents from
 * @param[out] ospf_type	The OSPF packet type
 * @param[in, out] remaining	Updated with the number of captured bytes remaining
 * @return A pointer to the first byte after the OSPF header.
 *
 * This function returns a void pointer that can be cast appropriately
 * based on the ospf_type. For example, if the ospf_type is TRACE_OSPF_HELLO 
 * then the return pointer should be cast as a libtrace_ospf_hello_v2_t 
 * structure.
 *
 * If the OSPF header is truncated, then NULL will be returned. If the OSPF 
 * contents are missing or truncated, the pointer to the start of the content 
 * will still be returned so be careful to check the value of remaining.
 *
 * 'remaining' MUST be set to the amount of bytes remaining in the captured
 * packet starting from the beginning of the OSPF header. It will be updated
 * to contain the number of bytes remaining from the start of the OSPF contents.
 *
 * @note This function only works for OSPF version 2 packets.
 * @note Use trace_get_first_ospf_lsa_v2_from_X() and trace_get_next_ospf_lsa_v2() to read the LSAs from Link State Update packets.
 * @note Use trace_get_first_ospf_lsa_v2_from_X() and trace_get_next_ospf_lsa_header_v2() to read the LSA headers from Link State Ack packets.
 * 
 */ 
DLLEXPORT SIMPLE_FUNCTION
void *trace_get_ospf_contents_v2(libtrace_ospf_v2_t *header,
		uint8_t *ospf_type, uint32_t *remaining);

/** Get a pointer to the start of the first LSA contained within an LS Update packet
 * @param ls_update	Pointer to the LS Update header
 * @param[in,out] remaining	Updated with the number of captured bytes remaining
 * @return A pointer to the first LSA in the packet.
 *
 * This function simply skips past the LS Update header to provide a suitable
 * pointer to pass into trace_get_next_ospf_lsa_v2.
 *
 * If the OSPF packet is truncated, then NULL will be returned.
 *
 * 'remaining' MUST be set to the amount of bytes remaining in the captured
 * packet starting from the beginning of the LS Update header. It will be 
 * updated to contain the number of bytes remaining from the start of the 
 * first LSA.
 *
 * @note This function only works for OSPF version 2 packets.
 * @note trace_get_next_ospf_lsa_v2() should be subsequently used to process the LSAs
 */
DLLEXPORT SIMPLE_FUNCTION 
unsigned char *trace_get_first_ospf_lsa_from_update_v2(
                libtrace_ospf_ls_update_t *ls_update,
                uint32_t *remaining);

/** Get a pointer to the start of the first LSA contained within an Database Description packet
 * @param db_desc	Pointer to the Database Description header
 * @param[in,out] remaining	Updated with the number of captured bytes remaining
 * @return A pointer to the first LSA in the packet.
 *
 * This function simply skips past the Database Description header to provide a 
 * suitable pointer to pass into trace_get_next_ospf_lsa_header_v2.
 *
 * If the OSPF packet is truncated, then NULL will be returned.
 *
 * 'remaining' MUST be set to the amount of bytes remaining in the captured
 * packet starting from the beginning of the Database Description header. It 
 * will be updated to contain the number of bytes remaining from the start of 
 * the first LSA.
 *
 * @note This function only works for OSPF version 2 packets.
 * @note trace_get_next_ospf_lsa_header_v2() should be subsequently used to process the LSA headers
 */
DLLEXPORT SIMPLE_FUNCTION 
unsigned char *trace_get_first_ospf_lsa_from_db_desc_v2(
                libtrace_ospf_db_desc_v2_t *db_desc,
                uint32_t *remaining);

/** Get a pointer to the start of the first link contained within a Router LSA
 * @param lsa	Pointer to the Router LSA
 * @param[in,out] remaining	Updated with the number of captured bytes remaining
 * @return A pointer to the first link in the packet.
 *
 * This function simply skips past the Router LSA header to provide a 
 * suitable pointer to pass into trace_get_next_ospf_link_v2.
 *
 * If the OSPF packet is truncated, then NULL will be returned.
 *
 * 'remaining' MUST be set to the amount of bytes remaining in the captured
 * packet starting from the beginning of the Router LSA (not including the LSA 
 * header) header. It will be updated to contain the number of bytes remaining 
 * from the start of the first Link.
 *
 * @note This function only works for OSPF version 2 packets.
 * @note trace_get_next_ospf_link_v2() should be subsequently used to process
 * the links
 */
DLLEXPORT SIMPLE_FUNCTION
unsigned char *trace_get_first_ospf_link_from_router_lsa_v2(
		libtrace_ospf_router_lsa_v2_t *lsa,
		uint32_t *remaining);

/** Parses an OSPF Router LSA Link and finds the next Link (if there is one)
 * @param[in,out] current	Pointer to the next Link (updated by this function)
 * @param[out] link		Set to point to the Link located at the original value of current
 * @param[in,out] remaining	Updated with the number of captured bytes remaining
 * @param[out] link_len		Set to the size of the Link pointed to by 'link'
 * @return 0 if there are no more links after the current one, 1 otherwise.
 *
 * When called, 'current' MUST point to an OSPF Router LSA link. Ideally, this
 * would come from either a call to 
 * trace_get_first_ospf_link_from_router_lsa_v2() or a previous call of this
 * function. 
 *
 * 'link' will be set to the value of 'current', so that the caller may then
 * do any processing they wish on that particular link. 'current' is advanced
 * to point to the next link and 'link_len' is updated to report the size of
 * the original link.
 *
 * 'remaining' MUST be set to the amount of bytes remaining in the captured
 * packet starting from the beginning of the Link pointed to by 'current'.
 * It will be updated to contain the number of bytes remaining from the start 
 * of the next link.
 *
 * If this function returns 0 but 'link' is NOT NULL, that link is still valid
 * but there are no more links after this one.
 * If this function returns 0 AND link is NULL, the link is obviously not 
 * suitable for processing. 
 *
 * @note This function only works for OSPF version 2 packets.
 */
DLLEXPORT SIMPLE_FUNCTION
int trace_get_next_ospf_link_v2(unsigned char **current,
		libtrace_ospf_link_v2_t **link,
		uint32_t *remaining,
		uint32_t *link_len);

/** Parses an OSPF LSA and finds the next LSA (if there is one)
 * @param[in,out] current 	Pointer to the next LSA (updated by this function)
 * @param[out] lsa_hdr		Set to point to the header of the LSA located at the original value of current
 * @param[out] lsa_body		Set to point to the body of the LSA located at the original value of current
 * @param[in,out] remaining	Updated with the number of captured bytes remaining
 * @param[out] lsa_type		Set to the type of the LSA located at the original value of current
 * @param[out] lsa_length	Set to the size of the LSA located at the original value of current
 * @return 1 if there are more LSAs after the current one, 0 if there are no more LSAs to come, and -1 if the current LSA is incomplete, truncated or invalid.
 *
 * When called, 'current' MUST point to an OSPF LSA. Ideally, this would come 
 * from either a call to trace_get_first_ospf_lsa_from_update_v2() or a 
 * previous call of this function. 
 *
 * This function should only be used to access COMPLETE LSAs, i.e. LSAs that
 * have both a header and a body. In OSPFv2, only the LSAs contained within
 * LSA Update packets meet this requirement. trace_get_next_ospf_lsa_header_v2
 * should be used to read header-only LSAs, e.g. those present in LS Acks.
 *
 * 'lsa_hdr' will be set to the value of 'current', so that the caller may then
 * do any processing they wish on that particular LSA. 'lsa_body' will be set
 * to point to the first byte after the LSA header. 'current' is advanced
 * to point to the next LSA. 'lsa_length' is updated to contain the size of
 * the parsed LSA, while 'lsa_type' is set to indicate the LSA type.
 *
 * 'remaining' MUST be set to the amount of bytes remaining in the captured
 * packet starting from the beginning of the LSA pointed to by 'current'.
 * It will be updated to contain the number of bytes remaining from the start 
 * of the next LSA.
 *
 * If this function returns 0 but 'lsa_hdr' is NOT NULL, that LSA is still 
 * valid but there are no more LSAs after this one.
 * If this function returns 0 AND 'lsa_hdr' is NULL, the LSA is obviously not 
 * suitable for processing. 
 *
 * It is also recommended to check the value of 'lsa_body' before 
 * de-referencing it. 'lsa_body' will be set to NULL if there is only an LSA
 * header present.
 * 
 * @note This function only works for OSPF version 2 packets.
 *
 */
DLLEXPORT SIMPLE_FUNCTION
int trace_get_next_ospf_lsa_v2(unsigned char **current,
                libtrace_ospf_lsa_v2_t **lsa_hdr,
                unsigned char **lsa_body,
                uint32_t *remaining,
                uint8_t *lsa_type,
                uint16_t *lsa_length);

/** Parses an OSPF LSA header and finds the next LSA (if there is one)
 * @param[in,out] current 	Pointer to the next LSA (updated by this function)
 * @param[out] lsa_hdr		Set to point to the header of the LSA located at the original value of current
 * @param[in,out] remaining	Updated with the number of captured bytes remaining
 * @param[out] lsa_length	Set to the size of the LSA located at the original value of current
 * @return 1 if there are more LSAs after the current one, 0 if there are no more LSAs to come, and -1 if the current LSA is incomplete, truncated or invalid.
 *
 * When called, 'current' MUST point to an OSPF LSA. Ideally, this would come 
 * from either a call to trace_get_first_ospf_lsa_from_db_desc_v2() or a 
 * previous call of this function. 
 *
 * This function should only be used to access LSA headers, i.e. LSAs that
 * have a header only. In OSPFv2, the LSAs contained within LSA Ack and 
 * Database Description packets meet this requirement. 
 * trace_get_next_ospf_lsa_v2 should be used to read full LSAs, e.g. those 
 * present in LS Updates.
 *
 * 'lsa_hdr' will be set to the value of 'current', so that the caller may then
 * do any processing they wish on that particular LSA header. 'current' is 
 * advanced to point to the next LSA header. 'lsa_length' is updated to contain 
 * the size of the parsed LSA header.
 *
 * 'remaining' MUST be set to the amount of bytes remaining in the captured
 * packet starting from the beginning of the LSA pointed to by 'current'.
 * It will be updated to contain the number of bytes remaining from the start 
 * of the next LSA.
 *
 * If this function returns 0 but 'lsa_hdr' is NOT NULL, that LSA is still 
 * valid but there are no more LSAs after this one.
 * If this function returns 0 AND 'lsa_hdr' is NULL, the LSA is obviously not 
 * suitable for processing. 
 *
 * @note This function only works for OSPF version 2 packets.
 *
 */
DLLEXPORT SIMPLE_FUNCTION
int trace_get_next_ospf_lsa_header_v2(unsigned char **current,
                libtrace_ospf_lsa_v2_t **lsa_hdr,
                uint32_t *remaining,
                uint8_t *lsa_type,
                uint16_t *lsa_length); 

/** Extracts the metric field from an AS External LSA packet
 *
 * @param as_lsa	The AS External LSA
 * @returns The value of the metric field
 *
 * The metric field in the AS External LSA packet is a 24-bit value, which
 * is difficult to extract correctly. To avoid byte-ordering issues, use this
 * function which will extract the correct value for you.
 */
DLLEXPORT SIMPLE_FUNCTION
uint32_t trace_get_ospf_metric_from_as_external_lsa_v2(
		libtrace_ospf_as_external_lsa_v2_t *as_lsa);

/** Extracts the metric field from a Summary LSA packet
 *
 * @param sum_lsa	The Summary LSA
 * @returns The value of the metric field
 *
 * The metric field in the Summary LSA packet is a 24-bit value, which
 * is difficult to extract correctly. To avoid byte-ordering issues, use this
 * function which will extract the correct value for you.
 */
DLLEXPORT SIMPLE_FUNCTION
uint32_t trace_get_ospf_metric_from_summary_lsa_v2(
		libtrace_ospf_summary_lsa_v2_t *sum_lsa);


/** Gets the destination MAC address for a given packet
 * @param packet  	The packet to extract the destination MAC address from
 *
 * @return A pointer to the destination MAC address field in the layer 2 
 * header, (or NULL if there is no destination MAC address or layer 2 header
 * available)
 *
 * @note This is a zero-copy function, so the memory that the returned pointer
 * points to is part of the packet itself. 
 */
DLLEXPORT SIMPLE_FUNCTION
uint8_t *trace_get_destination_mac(libtrace_packet_t *packet);

/** Gets the source MAC address for a given packet
 * @param packet  	The packet to extract the source MAC address from
 *
 * @return A pointer to the source MAC address field in the layer 2 
 * header, (or NULL if there is no source MAC address or layer 2 header
 * available)
 *
 * @note This is a zero-copy function, so the memory that the returned pointer
 * points to is part of the packet itself. 
 */
DLLEXPORT SIMPLE_FUNCTION
uint8_t *trace_get_source_mac(libtrace_packet_t *packet);

/** Get the source IP address for a given packet
 * @param packet  	The packet to extract the source IP address from
 * @param addr		A pointer to a sockaddr structure to store the address 
 * 			in. If NULL, static storage is used instead.
 * @return A pointer to a sockaddr holding a v4 or v6 IP address or on some 
 * platforms a sockaddr holding a MAC address. Returns NULL if no source IP
 * address was available.
 *
 * @note The best way to use this function is to pass in a pointer to the
 * struct sockaddr_storage for the addr parameter. This will avoid problems
 * with trying to shoe-horn an IPv6 address into a sockaddr that only supports
 * IPv4.
 */
DLLEXPORT SIMPLE_FUNCTION
struct sockaddr *trace_get_source_address(const libtrace_packet_t *packet,
		struct sockaddr *addr);

/** Get the source IP address for a packet and convert it into a string
 * @param packet	The packet to extract the source IP address from
 * @param space		A pointer to a character buffer to store the address 
 *			in. If NULL, static storage is used instead.
 * @param spacelen	The size of the buffer passed in via 'space'. Set this
 *			to zero if you are going to pass in a NULL buffer.
 * @return A pointer to a character buffer containing the string representation
 * of the source IP address. For packets where there is no suitable IP address,
 * the source MAC will be returned instead. Returns NULL if no valid address
 * is available.
 *
 * @note Be wary of the possibility of the address being an IPv6 address - make
 * sure your buffer is large enough!
 *
 * New in libtrace 3.0.17.
 */
DLLEXPORT SIMPLE_FUNCTION
char *trace_get_source_address_string(const libtrace_packet_t *packet,
		char *space, int spacelen);

/** Get the destination IP address for a given packet
 * @param packet  	The packet to extract the destination IP address from
 * @param addr		A pointer to a sockaddr structure to store the address 
 * 			in. If NULL, static storage is used instead.
 * @return A pointer to a sockaddr holding a v4 or v6 IP address or on some 
 * platforms a sockaddr holding a MAC address. Returns NULL if no destination 
 * IP address was available.
 *
 * @note The best way to use this function is to pass in a pointer to the
 * struct sockaddr_storage for the addr parameter. This will avoid problems
 * with trying to shoe-horn an IPv6 address into a sockaddr that only supports
 * IPv4.
 */
DLLEXPORT SIMPLE_FUNCTION
struct sockaddr *trace_get_destination_address(const libtrace_packet_t *packet,
		struct sockaddr *addr);

/** Get the destination IP address for a packet and convert it into a string
 * @param packet	The packet to extract the destination IP address from
 * @param space		A pointer to a character buffer to store the address 
 *			in. If NULL, static storage is used instead.
 * @param spacelen	The size of the buffer passed in via 'space'. Set this
 *			to zero if you are going to pass in a NULL buffer.
 * @return A pointer to a character buffer containing the string representation
 * of the destination IP address. For packets where there is no suitable IP 
 * address, the destination MAC will be returned instead. Returns NULL if no 
 * valid address is available.
 *
 * @note Be wary of the possibility of the address being an IPv6 address - make
 * sure your buffer is large enough!
 *
 * New in libtrace 3.0.17.
 */
DLLEXPORT SIMPLE_FUNCTION
char *trace_get_destination_address_string(const libtrace_packet_t *packet,
		char *space, int spacelen);

/** Parses an IP or TCP option
 * @param[in,out] ptr	The pointer to the current option
 * @param[in,out] len	The total length of all the remaining options
 * @param[out] type	The type of the option
 * @param[out] optlen 	The length of the option
 * @param[out] data	The data of the option
 *
 * @return bool true if there is another option (and the fields are filled in)
 *               or false if this was the last option.
 *
 * This updates ptr to point to the next option after this one, and updates
 * len to be the number of bytes remaining in the options area.  Type is updated
 * to be the code of this option, and data points to the data of this option,
 * with optlen saying how many bytes there are.
 *
 * @note Beware of fragmented packets.
 */
DLLEXPORT int trace_get_next_option(unsigned char **ptr,int *len,
			unsigned char *type,
			unsigned char *optlen,
			unsigned char **data);

/*@}*/

/** @name Time
 * These functions deal with the timestamp describing when a packet was 
 * captured and can convert it into various formats
 * @{
 */

/** Get the packet timestamp in the DAG time format 
 * @param packet  	The packet to extract the timestamp from
 *
 * @return a 64 bit timestamp in DAG ERF format (upper 32 bits are the seconds
 * past 1970-01-01, the lower 32bits are partial seconds)
 */
DLLEXPORT SIMPLE_FUNCTION
uint64_t trace_get_erf_timestamp(const libtrace_packet_t *packet);

/** Get the packet timestamp as a struct timeval
 * @param packet  	The packet to extract the timestamp from
 *
 * @return The time that this packet was captured in a struct timeval
 */ 
DLLEXPORT SIMPLE_FUNCTION
struct timeval trace_get_timeval(const libtrace_packet_t *packet);

/** Get the packet timestamp as a struct timespec
 * @param packet  	The packet to extract the timestamp from
 *
 * @return The time that this packet was captured in a struct timespec
 */ 
DLLEXPORT SIMPLE_FUNCTION
struct timespec trace_get_timespec(const libtrace_packet_t *packet);

/** Get the packet timestamp in floating point seconds
 * @param packet  	The packet to extract the timestamp from
 *
 * @return time that this packet was seen in 64-bit floating point seconds from
 * the UNIX epoch (1970-01-01 00:00:00 UTC).
 */
DLLEXPORT SIMPLE_FUNCTION
double trace_get_seconds(const libtrace_packet_t *packet);

/** Seek within an input trace to a time specified in floating point seconds
 * @param trace		The input trace to seek within
 * @param seconds	The time to seek to, in floating point seconds
 * @return 0 on success, -1 if the seek fails. Use trace_perror() to determine
 * the error that occurred.
 *
 * This will make the next packet read to be the first packet to occur at or 
 * after the specified time.  This must be called in the configuration state 
 * (i.e. before trace_start() or after trace_pause()).
 *
 * The time format accepted by this function is 64-bit floating point seconds
 * since the UNIX epoch (1970-01-01 00:00:00 UTC), i.e. the same format as
 * trace_get_seconds().
 *
 * @note This function may be extremely slow.
 */
DLLEXPORT int trace_seek_seconds(libtrace_t *trace, double seconds);

/** Seek within an input trace to a time specified as a timeval
 * @param trace		The input trace to seek within
 * @param tv		The time to seek to, as a timeval
 *
 * @return 0 on success, -1 if the seek fails. Use trace_perror() to determine
 * the error that occurred.
 *
 * This will make the next packet read to be the first packet to occur at or 
 * after the specified time.  This must be called in the configuration state 
 * (i.e. before trace_start() or after trace_pause()).
 *
 * @note This function may be extremely slow.
 */
DLLEXPORT int trace_seek_timeval(libtrace_t *trace, struct timeval tv);

/** Seek within an input trace to a time specified as an ERF timestamp
 * @param trace		The input trace to seek within
 * @param ts		The time to seek to, as an ERF timestamp
 *
 * @return 0 on success, -1 if the seek fails. Use trace_perror() to determine
 * the error that occurred.
 *
 * This will make the next packet read to be the first packet to occur at or 
 * after the specified time.  This must be called in the configuration state 
 * (i.e. before trace_start() or after trace_pause()).
 *
 * The time format accepted by this function is the ERF timestamp, which is a
 * 64-bit value where the upper 32 bits are seconds since the UNIX epoch and
 * the lower 32 bits are partial seconds.
 *
 * @note This function may be extremely slow.
 */
DLLEXPORT int trace_seek_erf_timestamp(libtrace_t *trace, uint64_t ts);

/*@}*/

/** @name Sizes
 * This section deals with finding or setting the various different lengths
 * that a packet can have, e.g. capture lengths, wire lengths, etc.
 * @{
 */
/** Get the current size of the packet (in bytes), taking into account any 
 * truncation or snapping that may have previously been performed. 
 *
 * @param packet  	The packet to determine the capture length for
 * @return The size of the packet read from the input trace, i.e. what is
 * actually available to libtrace at the moment.
 *
 * @note Most traces are header captures, so this value may not be the same
 * as the size of the packet when it was captured. Use trace_get_wire_length()
 * to get the original size of the packet.
 
 * @note This can (and often is) different for different packets in a trace!
 
 * @note This is sometimes called the "snaplen".
 *
 * @note The return size refers to the network-level payload of the packet and
 * does not include any capture framing headers. For example, an Ethernet 
 * packet with an empty TCP packet will return sizeof(ethernet_header) + 
 * sizeof(ip_header) + sizeof(tcp_header), but not the capture format
 * (pcap/erf/etc) header.
 */
DLLEXPORT SIMPLE_FUNCTION
size_t trace_get_capture_length(const libtrace_packet_t *packet);

/** Get the size of the packet as it was originally seen on the wire (in bytes).
 * @param packet  	The packet to determine the wire length for
 * @return The size of the packet as it was on the wire.
 *
 * @note This value may not be the same as the capture length, due to 
 * truncation.
 *
 * @note trace_get_wire_length \em includes  the Frame Check Sequence. This is 
 * different behaviour compared to most PCAP-based tools.
 *
 * @note The return size refers to the network-level payload of the packet and
 * does not include any capture framing headers. For example, an Ethernet 
 * packet with an empty TCP packet will return sizeof(ethernet_header) + 
 * sizeof(ip_header) + sizeof(tcp_header), but not the capture format
 * (pcap/erf/etc) header.
 */ 
DLLEXPORT SIMPLE_FUNCTION
size_t trace_get_wire_length(const libtrace_packet_t *packet);

/** Get the length of the capture framing headers (in bytes).
 * @param packet  	The packet to determine the framing length for
 * @return The size of the capture format header encapsulating the packet.
 *
 * @note This length corresponds to the difference between the amount of
 * memory required to store a captured packet and the capture length reported
 * by trace_capture_length()
 */ 
DLLEXPORT SIMPLE_FUNCTION
size_t trace_get_framing_length(const libtrace_packet_t *packet);

/** Get the length of the original payload content of the packet (in bytes).
 * @param packet	The packet to determine the payload length for
 * @return The size of the packet payload (without headers). Returns 0 if
 * unable to calculate payload length correctly.
 *
 * This function reports the amount of data that followed the transport header
 * when the packet was originally captured, i.e. prior to any snapping. Best
 * described as the wire length minus the packet headers. 
 *
 * Currently only supports some protocols and will return 0 if an unsupported
 * protocol header is encountered, or if one of the headers is truncated. 
 *
 * @note Supports IPv4, IPv6, TCP, UDP and ICMP.
 */ 
DLLEXPORT SIMPLE_FUNCTION
size_t trace_get_payload_length(const libtrace_packet_t *packet);

/** Truncate ("snap") the packet to the suggested length
 * @param packet	The packet to truncate
 * @param size		The new length of the packet (in bytes)
 *
 * @return The new capture length of the packet or the original capture
 * length of the packet if unchanged.
 *
 * This function will modify the capture length of the given packet. The wire
 * length will not be changed, so you can always determine what the original
 * packet size was, prior to the truncation.
 *
 * @note You can only use this function to decrease the capture length. Any
 * attempt to increase capture length will have no effect.
 */
DLLEXPORT size_t trace_set_capture_length(libtrace_packet_t *packet, size_t size);

/*@}*/


/** Gets the link layer type for a packet
 * @param packet  	The packet to extract the link layer type for
 * @return A libtrace_linktype_t describing the link layer protocol being used
 * by this packet.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_linktype_t trace_get_link_type(const libtrace_packet_t *packet);

/** Set the direction flag for a packet, if the capture format supports
 * direction tagging.
 *
 * @param packet  	The packet to set the direction for
 * @param direction	The new direction 
 * @returns -1 on error, or the direction that was set.
 *
 * @note Few capture formats actually support direction tagging. Most notably,
 * we cannot set the direction on PCAP packets.
 */
DLLEXPORT libtrace_direction_t trace_set_direction(libtrace_packet_t *packet, libtrace_direction_t direction);

/** Get the direction flag for a packet, if it has one.
 * @param packet  The packet to get the direction for
 *
 * @return A value representing the direction flag, or -1 if this is not 
 * supported by the capture format.
 * 
 * The direction is defined as 0 for packets originating locally (ie, outbound)
 * and 1 for packets originating remotely (ie, inbound). Other values are 
 * possible, which might be overloaded to mean special things for certain 
 * traces, e.g. in the Waikato traces, 2 is used to represent an "Unknown"
 * direction.
 *
 * For DAG/ERF traces, the direction is extracted from the "Interface" bits in 
 * the ERF header, which can range from 0 - 3.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_direction_t trace_get_direction(const libtrace_packet_t *packet);

/** @name BPF
 * This section deals with using Berkley Packet Filters to filter input traces
 * @{
 */
/** Creates a BPF filter
 * @param filterstring The filter string describing the BPF filter to create
 * @return An opaque pointer to a libtrace_filter_t object
 *
 * @note The filter is not actually compiled at this point, so no correctness
 * tests are performed here. trace_create_filter() will always return ok, but
 * if the filter is poorly constructed an error will be generated when the 
 * filter is actually used.
 */
DLLEXPORT SIMPLE_FUNCTION
libtrace_filter_t *trace_create_filter(const char *filterstring);

/** Create a BPF filter based on pre-compiled byte-code.
 * @param bf_insns	A pointer to the start of the byte-code
 * @param bf_len	The number of BPF instructions	
 * @return		An opaque pointer to a libtrace_filter_t object
 * @note		The supplied byte-code is not checked for correctness.
 * 			Instead, incorrect byte-code will generate an error
 * 			once the filter is actually used.
 * @author		Scott Raynel
 */
DLLEXPORT libtrace_filter_t *
trace_create_filter_from_bytecode(void *bf_insns, unsigned int bf_len);

/** Apply a BPF filter to a packet
 * @param filter 	The filter to be applied	
 * @param packet	The packet to be matched against the filter
 * @return >0 if the filter matches, 0 if it doesn't, -1 on error.
 * 
 * @note Due to the way BPF filters are built, the filter is not actually
 * compiled until the first time trace_apply_filter is called. If your filter
 * is incorrect, it will generate an error message and assert, exiting the
 * program. This behaviour may change to a more graceful handling of this error
 * in the future.
 */
DLLEXPORT int trace_apply_filter(libtrace_filter_t *filter,
		const libtrace_packet_t *packet);

/** Destroy a BPF filter
 * @param filter 	The filter to be destroyed
 * 
 * Deallocates all the resources associated with a BPF filter.
 */
DLLEXPORT void trace_destroy_filter(libtrace_filter_t *filter);
/*@}*/

/** @name Portability
 * This section contains functions that deal with portability issues, e.g. byte
 * ordering.
 * @{
 */

/** Converts an ethernet address to a printable string 
 * @param addr 	Ethernet address in network byte order
 * @param buf	Buffer to store the ascii representation, or NULL to indicate
 * that static storage should be used.
 * @return buf, or if buf is NULL then a statically allocated buffer.
 *
 * This function is similar to the GNU ether_ntoa_r function, with a few
 * minor differences.  If NULL is passed as buf, then the function will
 * use an internal static buffer. If NULL isn't passed then the function
 * will use that buffer instead.
 *
 * The address pointers returned by trace_get_source_mac() and 
 * trace_get_destination_mac() can be passed directly into this function.
 *
 * @note The type of addr isn't struct ether_addr as it is with ether_ntoa_r,
 * however it is bit compatible so that a cast will work.
 */ 
DLLEXPORT char *trace_ether_ntoa(const uint8_t *addr, char *buf);

/** Convert a string to an ethernet address
 * @param buf	A string containing an Ethernet address in hex format 
 * delimited with :'s.
 * @param addr	Buffer to store the binary representation, or NULL to indicate
 * that static storage should be used.
 * @return addr, or if addr is NULL then a statically allocated buffer.
 *
 * This function is similar to the GNU ether_aton_r function, with a few
 * minor differences.  If NULL is passed as addr, then the function will
 * use an internal static buffer. If NULL isn't passed then the function will 
 * use that buffer instead.
 * 
 * The address returned by this function will be in network byte order.
 *
 * @note the type of addr isn't struct ether_addr as it is with ether_aton_r,
 * however it is bit compatible so that a cast will work.
 */
DLLEXPORT uint8_t *trace_ether_aton(const char *buf, uint8_t *addr);

/*@}*/

/** @name Ports
 * This section contains functions for dealing with port numbers at the 
 * transport layer.
 *
 * @{
 */

/** An indication of which port is the "server" port for a given port pair */
typedef enum {
	USE_DEST, 	/**< Destination port is the server port */
	USE_SOURCE	/**< Source port is the server port */
} serverport_t;

/** Gets the source port for a given packet
 * @param packet	The packet to get the source port from
 * @return The source port in HOST byte order or 0 if no suitable port number
 * can be extracted from the packet.
 *
 * This function will return 0 if the transport protocol is known not to
 * use port numbers, e.g. ICMP. 0 is also returned if no transport header is
 * present in the packet or the transport header has been truncated such that
 * the port fields are not readable.
 *
 * @note If the transport protocol is not known by libtrace, the first two
 * bytes of the transport header will be treated as the source port field.
 */
DLLEXPORT SIMPLE_FUNCTION
uint16_t trace_get_source_port(const libtrace_packet_t *packet);

/** Gets the destination port for a given packet
 * @param packet	The packet to get the destination port from
 * @return The destination port in HOST byte order or 0 if no suitable port
 * number can be extracted from the packet.
 *
 * This function will return 0 if the transport protocol is known not to
 * use port numbers, e.g. ICMP. 0 is also returned if no transport header is
 * present in the packet or the transport header has been truncated such that
 * the port fields are not readable.
 *
 * @note If the transport protocol is not known by libtrace, the third and
 * fourth bytes of the transport header will be treated as the destination 
 * port field.
 *
 */
DLLEXPORT SIMPLE_FUNCTION
uint16_t trace_get_destination_port(const libtrace_packet_t *packet);

/** Hint at which of the two provided ports is the server port.
 *
 * @param protocol	The IP layer protocol, eg 6 (tcp), 17 (udp)
 * @param source	The source port from the packet
 * @param dest		The destination port from the packet
 *
 * @return one of USE_SOURCE or USE_DEST describing on which of the two ports
 * is most likely to be the server port.
 *
 * @note Ports must be provided in HOST byte order!
 *
 * This function is based almost entirely on heuristics and should not be
 * treated as a definitive means of identifying the server port. However, it
 * is deterministic, so it is very handy for identifying both halves of the
 * same flow. 
 */
DLLEXPORT SIMPLE_FUNCTION
int8_t trace_get_server_port(uint8_t protocol, uint16_t source, uint16_t dest);

/*@}*/

/** @name Wireless trace support
 * Functions to access wireless information from packets that have wireless
 * monitoring headers such as Radiotap or Prism.
 * 
 * The trace_get_wireless_* functions provide an abstract interface for
 * retrieving information from wireless traces. They take a pointer to the
 * wireless monitoring header (usually found with trace_get_packet_meta()) and
 * the linktype of the header passed in.
 * 
 * All of the trace_get_wireless_* functions return false if the requested
 * information was unavailable, or true if it was. The actual data is stored
 * in an output variable supplied by the caller. Values returned into the 
 * output variable will always be returned in host byte order.
 * @{
 */


#ifndef ARPHRD_80211_RADIOTAP
/** libc doesn't define this yet, so we have to do so ourselves */
#define ARPHRD_80211_RADIOTAP 803
#endif

/** Get the wireless Timer Synchronisation Function
 *
 * Gets the value of the timer synchronisation function for this frame, which
 * is a value in microseconds indicating the time that the first bit of the
 * MPDU was received by the MAC.
 *
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in 
 * @param[out] tsft The value of the timer synchronisation function. 
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_tsft(void *linkptr,
        libtrace_linktype_t linktype, uint64_t *tsft);

/** Get the wireless data rate 
 *
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] rate The data-rate of the frame in units of 500kbps
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_rate(void *linkptr,
        libtrace_linktype_t linktype, uint8_t *rate);

/** Get the wireless channel frequency
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] freq The frequency in MHz of the channel the frame was 
 * transmitted or received on.
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_freq(void *linkptr,
        libtrace_linktype_t linktype, uint16_t *freq);

/** Get the wireless signal strength in dBm 
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] strength The RF signal power at the antenna, in dB difference
 * from 1mW.
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_signal_strength_dbm(void *linkptr,
        libtrace_linktype_t linktype, int8_t *strength);

/** Get the wireless noise strength in dBm
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] strength The RF noise power at the antenna, in dB difference 
 * from 1mW. 
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_noise_strength_dbm(void *linkptr,
        libtrace_linktype_t linktype, int8_t *strength);

/** Get the wireless signal strength in dB
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] strength The RF signal power at the antenna, in dB difference 
 * from a fixed reference. 
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_signal_strength_db(void *linkptr,
        libtrace_linktype_t linktype, uint8_t *strength);

/** Get the wireless noise strength in dB 
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] strength The RF noise power at the antenna, in dB difference 
 * from a fixed reference. 
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_noise_strength_db(void *linkptr,
        libtrace_linktype_t linktype, uint8_t *strength);

/** Get the wireless transmit attenuation 
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] attenuation The transmit power as a unitless distance from 
 * maximum power set at factory calibration. 0 indicates maximum transmission 
 * power.
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_tx_attenuation(void *linkptr,
        libtrace_linktype_t linktype, uint16_t *attenuation);

/** Get the wireless transmit attenuation in dB
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] attenuation The transmit power as dB difference from maximum 
 * power set at factory calibration. 0 indicates maximum power.
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_tx_attenuation_db(void *linkptr,
        libtrace_linktype_t linktype, uint16_t *attenuation);

/** Get the wireless transmit power in dBm 
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in 
 * @param[out] txpower The transmit power as dB from a 1mW reference. This is 
 * the absolute power level measured at the antenna port.  
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_tx_power_dbm(void *linkptr, 
		libtrace_linktype_t linktype, int8_t *txpower);

/** Get the wireless antenna 
 * @param linkptr The wireless meta header
 * @param linktype The linktype of the wireless meta header passed in
 * @param[out] antenna The antenna that was used to transmit or receive the 
 * frame.
 * @return true if the field was available, false if not.
 */
DLLEXPORT bool trace_get_wireless_antenna(void *linkptr,
        libtrace_linktype_t linktype, uint8_t *antenna);

/*@}*/

/* Destroy libtrace_meta_t structure
 *
 * @params libtrace_meta_t structure
 * returns 1 on success, -1 on failure
 */
DLLEXPORT int trace_destroy_meta(libtrace_meta_t *result);

/* Get the interface name/s for a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t meta packet.
 * @returns Pointer to libtrace_meta_t structure containing all found interface names
 * or NULL.
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_name_meta(libtrace_packet_t *packet);

/* Get the interface name for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the interface name from.
 * @params A pointer to a character buffer to store the interface name in.
 * @params The size of the buffer passed in.
 * @params The interface index within the meta packet.
 * @returns Pointer to the character buffer containing the interface name or NULL.
 */
DLLEXPORT char *trace_get_interface_name(libtrace_packet_t *packet, char *space, int spacelen,
	int index);

/* Get the interface MAC address/s for a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t meta packet.
 * @returns Pointer to libtrace_meta_t structure containing all found interface mac
 * addresses or NULL.
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_mac_meta(libtrace_packet_t *packet);

/* Get the interface MAC address for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the MAC address from.
 * @params A pointer to a character buffer to store the MAC address in.
 * @params The size of the buffer passed in.
 * @params The interface index within the meta packet.
 * @returns Pointer to the character buffer containing the MAC address or NULL.
 */
DLLEXPORT char *trace_get_interface_mac(libtrace_packet_t *packet, char *space, int spacelen,
        int index);

/* Get the interface speed/s from a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t packet.
 * @returns Pointer to libtrace_meta_t structure containing all found interface
 * speeds or NULL.
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_speed_meta(libtrace_packet_t *packet);

/* Get the interface speed for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the interface speed from.
 * @params The interface index within the meta packet.
 * @returns uint64_t interface speed or NULL.
 */
DLLEXPORT uint64_t trace_get_interface_speed(libtrace_packet_t *packet, int index);

/* Get the interface ipv4 address/s for a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t meta packet.
 * @returns Pointer to libtrace_meta_t structure containing all found ipv4 addresses
 * or NULL
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_ipv4_meta(libtrace_packet_t *packet);

/* Get the interface ipv4 address for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the ipv4 address from.
 * @params The interface index within the meta packet.
 * @returns uint32_t ipv4 address or 0.
 */
DLLEXPORT uint32_t trace_get_interface_ipv4(libtrace_packet_t *packet, int index);

/* Get the interface ipv4 address string for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the ipv4 address from.
 * @params A pointer to a character buffer to store the ipv4 address string in.
 * @params The size of the buffer passed in.
 * @params The interface index within the meta packet.
 * @returns Pointer to the character buffer containing the ipv4 address string or NULL.
 */
DLLEXPORT char *trace_get_interface_ipv4_string(libtrace_packet_t *packet, char* space, int spacelen,
	int index);

/* Get the interface ipv6 address/s for a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t meta packet.
 * @returns Pointer to libtrace_meta_t structure containing all found ipv6 addresses
 * or NULL.
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_ipv6_meta(libtrace_packet_t *packet);

/* Get the interface ipv6 address for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the ipv6 address from.
 * @params A pointer to a character buffer to store the ipv6 address in.
 * @params The size of the buffer passed in.
 * @params The interface index within the meta packet.
 * @returns Pointer to the buffer containing the ipv6 address or NULL.
 */
DLLEXPORT void *trace_get_interface_ipv6(libtrace_packet_t *packet, void *space, int spacelen,
	int index);

/* Get the interface ipv6 address string for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the ipv6 address from.
 * @params A pointer to a character buffer to store the ipv6 address in.
 * @params The size of the buffer passed in.
 * @params The interface index within the meta packet.
 * @returns Pointer to the character buffer containing the ipv6 address string or NULL.
 */
DLLEXPORT char *trace_get_interface_ipv6_string(libtrace_packet_t *packet, char *space, int spacelen,
	int index);

/* Get the interface description/s for a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t meta packet.
 * @returns Pointer to libtrace_meta_t structure containing all found interface
 * descriptions or NULL.
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_description_meta(libtrace_packet_t *packet);

/* Get the interface description for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the interface description from.
 * @params A pointer to a character buffer to store the interface description in.
 * @params The size of the buffer passed in.
 * @params The interface index within the meta packet.
 * @returns Pointer to the character buffer containing the interface description or NULL.
 */
DLLEXPORT char *trace_get_interface_description(libtrace_packet_t *packet, char *space, int spacelen,
	int index);

/* Get the host OS for a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t meta packet.
 * @returns Pointer to libtrace_meta_t structure containing the host OS or NULL.
 */
DLLEXPORT libtrace_meta_t *trace_get_host_os_meta(libtrace_packet_t *packet);

/* Get the host OS for a meta packet.
 *
 * @params libtrace_packet_t meta packet to extract the host OS from.
 * @params A pointer to a character buffer to store the host OS in.
 * @params The size of the buffer passed in.
 * @returns Pointer to the character buffer containing the host OS or NULL.
 */
DLLEXPORT char *trace_get_host_os(libtrace_packet_t *packet, char *space, int spacelen);

/* Get the interface frame check sequence length for a meta packet.
 * Must be destroyed with trace_destroy_meta().
 *
 * @params libtrace_packet_t meta packet.
 * @returns Pointer to libtrace_meta_t structure containing all found frame check
 * sequence lengths or NULL.
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_fcslen_meta(libtrace_packet_t *packet);

/* Get the interface frame check sequence length for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface index.
 *
 * @params libtrace_packet_t meta packet to extract the interface fcslen from.
 * @params The interface index within the meta packet.
 * @returns uint32_t frame check sequence length or 0.
 */
DLLEXPORT uint32_t trace_get_interface_fcslen(libtrace_packet_t *packet, int index);

/* Get any interface comments for a meta packet
 * Must be destroyed with trace_destroy_meta()
 *
 * @params libtrace_packet_t packet
 * @returns Pointer to libtrace_meta_t structure or NULL
 */
DLLEXPORT libtrace_meta_t *trace_get_interface_comment_meta(libtrace_packet_t *packet);

/* Get the interface comment for a meta packet.
 * Note: ERF packets can contain multiple interfaces per meta packet. Use index to
 * specify the interface ID.
 *
 * @params libtrace_packet_t meta packet to extract the interface comment from.
 * @params A pointer to a character buffer to store the interface description in.
 * @params The size of the buffer passed in.
 * @params The interface number within the meta packet.
 * @returns Pointer to the character buffer containing the hardware description or NULL.
 */
DLLEXPORT char *trace_get_interface_comment(libtrace_packet_t *packet, char *space, int spacelen,
	int index);

/* Get the capture application for a meta packet
 * Must be destroyed with trace_destroy_meta()
 *
 * @params libtrace_packet_t packet
 * @returns Pointer to libtrace_meta_t structure or NULL
 */
DLLEXPORT libtrace_meta_t *trace_get_capture_application_meta(libtrace_packet_t *packet);

/* Get the capture application for a meta packet.
 *
 * @params libtrace_packet_t meta packet to extract the application name from.
 * @params A pointer to a character buffer to store the application name in.
 * @params The size of the buffer passed in.
 * @returns Pointer to the character buffer containing the application name or NULL.
 */
DLLEXPORT char *trace_get_capture_application(libtrace_packet_t *packet, char *space, int spacelen);

/* Get a single specific meta-data field from a meta packet
 * Must be destroyed with trace_destroy_meta()
 *
 * @params packet               The meta packet to extract the option from
 * @params section_code         The section that the required option is found in
 * @params option_code          The code for the required option
 * @returns Pointer to libtrace_meta_t structure or NULL
 */
DLLEXPORT libtrace_meta_t *trace_get_single_meta_field(
        libtrace_packet_t *packet, uint32_t section_code, uint16_t option_code);

/* Parses all meta-data fields within a meta packet
 * Must be destroyed with trace_destroy_meta()
 *
 * @params libtrace_packet_t packet
 * @returns Pointer to libtrace_meta_t structure or NULL
 */
DLLEXPORT libtrace_meta_t *trace_get_all_metadata(libtrace_packet_t *packet);

/* Get the DAG card model from a meta packet.
 *
 * @params libtrace_packet_t meta packet to extract the DAG model from.
 * @params A pointer to a character buffer to store the DAG model in.
 * @params The size of the buffer passed in.
 * @returns Pointer to the character buffer containing the DAG model or NULL.
 */
DLLEXPORT char *trace_get_erf_dag_card_model(libtrace_packet_t *packet, char *space,
	int spacelen);

/* Get the host DAG software version for a meta packet.
 *
 * @params libtrace_packet_t meta packet to extract the hosts DAG verion from.
 * @params A pointer to a character buffer to store the DAG version in.
 * @params The size of the buffer passed in.
 * @returns Pointer to the character buffer containing the DAG version or NULL.
 */
DLLEXPORT char *trace_get_erf_dag_version(libtrace_packet_t *packet, char *space,
	int spacelen);

/* Get the firmware version for a DAG module from a meta packet.
 *
 * @params libtrace_packet_t meta packet to extract the FW version from.
 * @params A pointer to a character buffer to store the FW version in.
 * @params The size of the buffer passed in.
 * @returns Pointer to the character buffer containing the FW version or NULL.
 */
DLLEXPORT char *trace_get_erf_dag_fw_version(libtrace_packet_t *packet, char *space,
	int spacelen);

#ifdef __cplusplus
} /* extern "C" */
#endif /* #ifdef __cplusplus */

#endif /* LIBTRACE_H_ */
