/*
 * $Id: CError.h 1904 2006-04-23 17:44:42Z wlux $
 *
 * Copyright (c) 2005, Wolfgang Lux
 * See ../LICENSE for the full license.
 *
 * Foreign function wrappers for the CError library module
 */

#include <errno.h>

#ifndef E2BIG
# define E2BIG -1
#endif
#define e2BIG() E2BIG

#ifndef EACCES
# define EACCES -1
#endif
#define eACCES() EACCES

#ifndef EADDRINUSE
# define EADDRINUSE -1
#endif
#define eADDRINUSE() EADDRINUSE

#ifndef EADDRNOTAVAIL
# define EADDRNOTAVAIL -1
#endif
#define eADDRNOTAVAIL() EADDRNOTAVAIL

#ifndef EADV
# define EADV -1
#endif
#define eADV() EADV

#ifndef EAFNOSUPPORT
# define EAFNOSUPPORT -1
#endif
#define eAFNOSUPPORT() EAFNOSUPPORT

#ifndef EAGAIN
# define EAGAIN -1
#endif
#define eAGAIN() EAGAIN

#ifndef EALREADY
# define EALREADY -1
#endif
#define eALREADY() EALREADY

#ifndef EBADF
# define EBADF -1
#endif
#define eBADF() EBADF

#ifndef EBADMSG
# define EBADMSG -1
#endif
#define eBADMSG() EBADMSG

#ifndef EBADRPC
# define EBADRPC -1
#endif
#define eBADRPC() EBADRPC

#ifndef EBUSY
# define EBUSY -1
#endif
#define eBUSY() EBUSY

#ifndef ECHILD
# define ECHILD -1
#endif
#define eCHILD() ECHILD

#ifndef ECOMM
# define ECOMM -1
#endif
#define eCOMM() ECOMM

#ifndef ECONNABORTED
# define ECONNABORTED -1
#endif
#define eCONNABORTED() ECONNABORTED

#ifndef ECONNREFUSED
# define ECONNREFUSED -1
#endif
#define eCONNREFUSED() ECONNREFUSED

#ifndef ECONNRESET
# define ECONNRESET -1
#endif
#define eCONNRESET() ECONNRESET

#ifndef EDEADLK
# define EDEADLK -1
#endif
#define eDEADLK() EDEADLK

#ifndef EDESTADDRREQ
# define EDESTADDRREQ -1
#endif
#define eDESTADDRREQ() EDESTADDRREQ

#ifndef EDIRTY
# define EDIRTY -1
#endif
#define eDIRTY() EDIRTY

#ifndef EDOM
# define EDOM -1
#endif
#define eDOM() EDOM

#ifndef EDQUOT
# define EDQUOT -1
#endif
#define eDQUOT() EDQUOT

#ifndef EEXIST
# define EEXIST -1
#endif
#define eEXIST() EEXIST

#ifndef EFAULT
# define EFAULT -1
#endif
#define eFAULT() EFAULT

#ifndef EFBIG
# define EFBIG -1
#endif
#define eFBIG() EFBIG

#ifndef EFTYPE
# define EFTYPE -1
#endif
#define eFTYPE() EFTYPE

#ifndef EHOSTDOWN
# define EHOSTDOWN -1
#endif
#define eHOSTDOWN() EHOSTDOWN

#ifndef EHOSTUNREACH
# define EHOSTUNREACH -1
#endif
#define eHOSTUNREACH() EHOSTUNREACH

#ifndef EIDRM
# define EIDRM -1
#endif
#define eIDRM() EIDRM

#ifndef EILSEQ
# define EILSEQ -1
#endif
#define eILSEQ() EILSEQ

#ifndef EINPROGRESS
# define EINPROGRESS -1
#endif
#define eINPROGRESS() EINPROGRESS

#ifndef EINTR
# define EINTR -1
#endif
#define eINTR() EINTR

#ifndef EINVAL
# define EINVAL -1
#endif
#define eINVAL() EINVAL

#ifndef EIO
# define EIO -1
#endif
#define eIO() EIO

#ifndef EISCONN
# define EISCONN -1
#endif
#define eISCONN() EISCONN

#ifndef EISDIR
# define EISDIR -1
#endif
#define eISDIR() EISDIR

#ifndef ELOOP
# define ELOOP -1
#endif
#define eLOOP() ELOOP

#ifndef EMFILE
# define EMFILE -1
#endif
#define eMFILE() EMFILE

#ifndef EMLINK
# define EMLINK -1
#endif
#define eMLINK() EMLINK

#ifndef EMSGSIZE
# define EMSGSIZE -1
#endif
#define eMSGSIZE() EMSGSIZE

#ifndef EMULTIHOP
# define EMULTIHOP -1
#endif
#define eMULTIHOP() EMULTIHOP

#ifndef ENAMETOOLONG
# define ENAMETOOLONG -1
#endif
#define eNAMETOOLONG() ENAMETOOLONG

#ifndef ENETDOWN
# define ENETDOWN -1
#endif
#define eNETDOWN() ENETDOWN

#ifndef ENETRESET
# define ENETRESET -1
#endif
#define eNETRESET() ENETRESET

#ifndef ENETUNREACH
# define ENETUNREACH -1
#endif
#define eNETUNREACH() ENETUNREACH

#ifndef ENFILE
# define ENFILE -1
#endif
#define eNFILE() ENFILE

#ifndef ENOBUFS
# define ENOBUFS -1
#endif
#define eNOBUFS() ENOBUFS

#ifndef ENODATA
# define ENODATA -1
#endif
#define eNODATA() ENODATA

#ifndef ENODEV
# define ENODEV -1
#endif
#define eNODEV() ENODEV

#ifndef ENOENT
# define ENOENT -1
#endif
#define eNOENT() ENOENT

#ifndef ENOEXEC
# define ENOEXEC -1
#endif
#define eNOEXEC() ENOEXEC

#ifndef ENOLCK
# define ENOLCK -1
#endif
#define eNOLCK() ENOLCK

#ifndef ENOLINK
# define ENOLINK -1
#endif
#define eNOLINK() ENOLINK

#ifndef ENOMEM
# define ENOMEM -1
#endif
#define eNOMEM() ENOMEM

#ifndef ENOMSG
# define ENOMSG -1
#endif
#define eNOMSG() ENOMSG

#ifndef ENONET
# define ENONET -1
#endif
#define eNONET() ENONET

#ifndef ENOPROTOOPT
# define ENOPROTOOPT -1
#endif
#define eNOPROTOOPT() ENOPROTOOPT

#ifndef ENOSPC
# define ENOSPC -1
#endif
#define eNOSPC() ENOSPC

#ifndef ENOSR
# define ENOSR -1
#endif
#define eNOSR() ENOSR

#ifndef ENOSTR
# define ENOSTR -1
#endif
#define eNOSTR() ENOSTR

#ifndef ENOSYS
# define ENOSYS -1
#endif
#define eNOSYS() ENOSYS

#ifndef ENOTBLK
# define ENOTBLK -1
#endif
#define eNOTBLK() ENOTBLK

#ifndef ENOTCONN
# define ENOTCONN -1
#endif
#define eNOTCONN() ENOTCONN

#ifndef ENOTDIR
# define ENOTDIR -1
#endif
#define eNOTDIR() ENOTDIR

#ifndef ENOTEMPTY
# define ENOTEMPTY -1
#endif
#define eNOTEMPTY() ENOTEMPTY

#ifndef ENOTSOCK
# define ENOTSOCK -1
#endif
#define eNOTSOCK() ENOTSOCK

#ifndef ENOTTY
# define ENOTTY -1
#endif
#define eNOTTY() ENOTTY

#ifndef ENXIO
# define ENXIO -1
#endif
#define eNXIO() ENXIO

#ifndef EOPNOTSUPP
# define EOPNOTSUPP -1
#endif
#define eOPNOTSUPP() EOPNOTSUPP

#ifndef EPERM
# define EPERM -1
#endif
#define ePERM() EPERM

#ifndef EPFNOSUPPORT
# define EPFNOSUPPORT -1
#endif
#define ePFNOSUPPORT() EPFNOSUPPORT

#ifndef EPIPE
# define EPIPE -1
#endif
#define ePIPE() EPIPE

#ifndef EPROCLIM
# define EPROCLIM -1
#endif
#define ePROCLIM() EPROCLIM

#ifndef EPROCUNAVAIL
# define EPROCUNAVAIL -1
#endif
#define ePROCUNAVAIL() EPROCUNAVAIL

#ifndef EPROGMISMATCH
# define EPROGMISMATCH -1
#endif
#define ePROGMISMATCH() EPROGMISMATCH

#ifndef EPROGUNAVAIL
# define EPROGUNAVAIL -1
#endif
#define ePROGUNAVAIL() EPROGUNAVAIL

#ifndef EPROTO
# define EPROTO -1
#endif
#define ePROTO() EPROTO

#ifndef EPROTONOSUPPORT
# define EPROTONOSUPPORT -1
#endif
#define ePROTONOSUPPORT() EPROTONOSUPPORT

#ifndef EPROTOTYPE
# define EPROTOTYPE -1
#endif
#define ePROTOTYPE() EPROTOTYPE

#ifndef ERANGE
# define ERANGE -1
#endif
#define eRANGE() ERANGE

#ifndef EREMCHG
# define EREMCHG -1
#endif
#define eREMCHG() EREMCHG

#ifndef EREMOTE
# define EREMOTE -1
#endif
#define eREMOTE() EREMOTE

#ifndef EROFS
# define EROFS -1
#endif
#define eROFS() EROFS

#ifndef ERPCMISMATCH
# define ERPCMISMATCH -1
#endif
#define eRPCMISMATCH() ERPCMISMATCH

#ifndef ERREMOTE
# define ERREMOTE -1
#endif
#define eRREMOTE() ERREMOTE

#ifndef ESHUTDOWN
# define ESHUTDOWN -1
#endif
#define eSHUTDOWN() ESHUTDOWN

#ifndef ESOCKTNOSUPPORT
# define ESOCKTNOSUPPORT -1
#endif
#define eSOCKTNOSUPPORT() ESOCKTNOSUPPORT

#ifndef ESPIPE
# define ESPIPE -1
#endif
#define eSPIPE() ESPIPE

#ifndef ESRCH
# define ESRCH -1
#endif
#define eSRCH() ESRCH

#ifndef ESRMNT
# define ESRMNT -1
#endif
#define eSRMNT() ESRMNT

#ifndef ESTALE
# define ESTALE -1
#endif
#define eSTALE() ESTALE

#ifndef ETIME
# define ETIME -1
#endif
#define eTIME() ETIME

#ifndef ETIMEDOUT
# define ETIMEDOUT -1
#endif
#define eTIMEDOUT() ETIMEDOUT

#ifndef ETOOMANYREFS
# define ETOOMANYREFS -1
#endif
#define eTOOMANYREFS() ETOOMANYREFS

#ifndef ETXTBSY
# define ETXTBSY -1
#endif
#define eTXTBSY() ETXTBSY

#ifndef EUSERS
# define EUSERS -1
#endif
#define eUSERS() EUSERS

#ifndef EWOULDBLOCK
# define EWOULDBLOCK -1
#endif
#define eWOULDBLOCK() EWOULDBLOCK

#ifndef EXDEV
# define EXDEV -1
#endif
#define eXDEV() EXDEV
