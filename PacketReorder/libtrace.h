#include <stdint.h>
#include <pthread.h>

//JOSH - only include parts of libtrace.h that we need
//The file is just comprised of subsets of libtrace.h, with the following modifications
//1. in buf_control_t, changed char literals 'p' and 'e' to ints because of Verifast parse error
//2. remove pthread_mutex_t ref_lock from packet data structure because included pthread.h is too limited
//3. Change bitfields in ip and tcp structs to regular fields because Verifast does not support bitfields

#define LT_USE_PACKED 1
#if LT_USE_PACKED
#  define PACKED __attribute__((packed))
#else
#  define PACKED
#endif

#define LT_BITFIELD8        unsigned int

/** Opaque structure holding information about a trace */
typedef struct libtrace_t {} libtrace_t;

/** If the packet has allocated its own memory the buffer_control should be
 * set to TRACE_CTRL_PACKET, so that the memory will be freed when the packet
 * is destroyed. If the packet has been zero-copied out of memory owned by
 * something else, e.g. a DAG card, it should be TRACE_CTRL_EXTERNAL.
 *
 * @note The letters p and e are magic numbers used to detect if the packet
 * wasn't created properly.
 */
 //JOSH - had to convert from 'p' and 'e' to 
typedef enum {
	TRACE_CTRL_PACKET=112,  /**< Buffer memory is owned by the packet */
	TRACE_CTRL_EXTERNAL=101 /**< Buffer memory is owned by an external source */
} buf_control_t;

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
	TRACE_FORMAT_PFRING       =27
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
       TRACE_TYPE_XDP = 26            /** AF_XDP */
} libtrace_linktype_t;

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
        //pthread_mutex_t ref_lock;       /**< Lock for reference counter */
        // JOSH - not great, but looks like version of included pthread.h does not include whole library
        int refcount;                   /**< Reference counter */
        int which_trace_start;          /**< Used to match packet to a started instance of the parent trace */
} libtrace_packet_t;

//JOSH - from <netinet/in.h>
typedef uint32_t in_addr_t;
struct in_addr
  {
    in_addr_t s_addr;
  };


/** Generic IP header structure */
typedef struct libtrace_ip
{
#if __BYTE_ORDER == __LITTLE_ENDIAN
    LT_BITFIELD8 ip_hl;		/**< Header Length */
    LT_BITFIELD8 ip_v;		/**< Version */
#elif __BYTE_ORDER == __BIG_ENDIAN
    LT_BITFIELD8 ip_v;		/**< Version */
    LT_BITFIELD8 ip_hl;		/**< Header Length */
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

/*@

// For our purpose, we only care about the IP length fields. We need to know ultimately that the total length (ip_len) is at least as large as the ip header length + tcp header length

//Takes in head_len and len in bytes (NOT 32 bit words)
predicate libtrace_ip_p(libtrace_ip_t *ip, int head_len, int len) =
	ip != 0 &*& ip->ip_hl |-> ?head &*& 4 * head == head_len &*& ip->ip_len |-> len;

@*/

/** Generic TCP header structure */
typedef struct libtrace_tcp
  {
    uint16_t source;		/**< Source Port */
    uint16_t dest;		/**< Destination port */
    uint32_t seq;		/**< Sequence number */
    uint32_t ack_seq;		/**< Acknowledgement Number */
#  if __BYTE_ORDER == __LITTLE_ENDIAN
    LT_BITFIELD8 ecn_ns;      /**< ECN Nonce Sum */
    LT_BITFIELD8 res1;        /**< Reserved bits */
    LT_BITFIELD8 doff;        /**< Data Offset */
    LT_BITFIELD8 fin;         /**< FIN */
    LT_BITFIELD8 syn;         /**< SYN flag */
    LT_BITFIELD8 rst;         /**< RST flag */
    LT_BITFIELD8 psh;         /**< PuSH flag */
    LT_BITFIELD8 ack;         /**< ACK flag */
    LT_BITFIELD8 urg;         /**< URG flag */
    LT_BITFIELD8 ece;         /**< ECN Echo */
    LT_BITFIELD8 cwr;         /**< ECN CWR */
#  elif __BYTE_ORDER == __BIG_ENDIAN
    LT_BITFIELD8 doff;        /**< Data offset */
    LT_BITFIELD8 res1;        /**< Reserved bits */
    LT_BITFIELD8 ecn_ns;      /**< ECN Nonce Sum */
    LT_BITFIELD8 cwr;         /**< ECN CWR */
    LT_BITFIELD8 ece;         /**< ECN Echo */
    LT_BITFIELD8 urg;         /**< URG flag */
    LT_BITFIELD8 ack;         /**< ACK flag */
    LT_BITFIELD8 psh;         /**< PuSH flag */
    LT_BITFIELD8 rst;         /**< RST flag */
    LT_BITFIELD8 syn;         /**< SYN flag */
    LT_BITFIELD8 fin;         /**< FIN flag */
#  else
#   error "Adjust your <bits/endian.h> defines"
#  endif
    uint16_t window;		/**< Window Size */
    uint16_t check;		/**< Checksum */
    uint16_t urg_ptr;		/**< Urgent Pointer */
} PACKED libtrace_tcp_t;

/*@

//We need more information about the TCP structure, since we need to keep track of the header length, sequence number, and packet type

inductive tcp_type = syn | ack | fin | rst;

//Based on flags, what is tcp packet type?
//We differentiate between syn-ack, fin-ack, and just ack packets, since ack packets with no data will not increase the sequence number.
//Of the syn, fin, and rst flags, only 1 should be set to 1, though the ack flag may also be set in any of these.
fixpoint option<tcp_type> tcp_flags_to_type (int f_ack, int f_rst, int f_syn, int f_fin) {
	//SYN packet
	return (f_syn == 1 && f_fin == 0 && f_rst == 0 ? some(syn) :
	//FIN packet
	(f_fin == 1 && f_syn == 0 && f_rst == 0 ? some(fin) :
	//RST packet
	(f_rst == 1 && f_syn == 0 && f_fin == 0 ? some(rst) :
	//ACK packet
	(f_ack == 1 && f_syn == 0 && f_fin == 0 && f_rst == 0 ? some(ack) : none))));
}	

//NOTE: We need to differentiate between syn-ack, fin-ack, and ack packets, since ack packets do not increase the sequence number, while the others do


//TODO: handle ntohl and htons via axiomatizing

predicate libtrace_tcp_p (libtrace_tcp_t *tcp, int seq, int head_len, tcp_type ty) =
	tcp != 0 &*& tcp->doff |-> ?len &*& 4 * len == head_len &*& tcp->syn |-> ?syn &*& tcp->ack |-> ?ack &*& tcp->fin |-> ?fin &*& tcp->rst |-> ?rst &*&
	tcp_flags_to_type(ack, rst, syn, fin) == some(ty);

@*/

/*@
//Next, we need to deal with the trace_get_ip and trace_get_tcp functions. We need to know that these correspond to some (abstract) functions, which we can then use
//for a general predicate about well-formed TCP/IP libtrace packets. First, we need an abstract notion of a packet that is a valid IP packet
//TODO: do we need the lengths/seq/flags here?

predicate valid_ip_packet(libtrace_packet_t *packet, int head_len, int len);

predicate valid_tcp_packet(libtrace_packet_t *packet, int seq, int head_len, tcp_type ty);

//predicate valid_tcp_ip_packet(libtrace_packet_t *packet) = valid_ip_packet(packet) && valid_tcp_packet(packet);

@*/


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
//DLLEXPORT SIMPLE_FUNCTION
libtrace_ip_t *trace_get_ip(libtrace_packet_t *packet);
//@ requires valid_ip_packet(packet, ?head_len, ?len);
//@ ensures libtrace_ip_p(result, head_len, len);



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
//DLLEXPORT SIMPLE_FUNCTION
libtrace_tcp_t *trace_get_tcp(libtrace_packet_t *packet);
//@ requires valid_tcp_packet(packet, ?seq, ?head_len, ?ty);
//@ ensures libtrace_tcp_p(result, seq, head_len, ty);

/*@
//Valid Libtrace IP/TCP Packets

//TODO: do we need anything else in predicate?
predicate valid_packet(libtrace_packet_t *packet, int ip_head_len, int ip_len, int tcp_head_len, int seq, int plen, tcp_type ty) =
	valid_tcp_packet(packet, seq, tcp_head_len, ty) &*& valid_ip_packet(packet, ip_head_len, ip_len) &*& plen == ip_len - ip_head_len - tcp_head_len &*&
	plen >= 0;
	@*/
