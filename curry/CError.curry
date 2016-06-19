-- $Id: CError.curry 3243 2016-06-19 12:37:10Z wlux $
--
-- Copyright (c) 2005-2015, Wolfgang Lux
-- See ../LICENSE for the full license.

module CError(Errno(..), eOK, e2BIG, eACCES, eADDRINUSE, eADDRNOTAVAIL,
              eADV, eAFNOSUPPORT, eAGAIN, eALREADY, eBADF, eBADMSG, eBADRPC,
              eBUSY, eCHILD, eCOMM, eCONNABORTED, eCONNREFUSED, eCONNRESET,
              eDEADLK, eDESTADDRREQ, eDIRTY, eDOM, eDQUOT, eEXIST, eFAULT,
              eFBIG, eFTYPE, eHOSTDOWN, eHOSTUNREACH, eIDRM, eILSEQ,
              eINPROGRESS, eINTR, eINVAL, eIO, eISCONN, eISDIR, eLOOP,
              eMFILE, eMLINK, eMSGSIZE, eMULTIHOP, eNAMETOOLONG, eNETDOWN,
              eNETRESET, eNETUNREACH, eNFILE, eNOBUFS, eNODATA, eNODEV,
              eNOENT, eNOEXEC, eNOLCK, eNOLINK, eNOMEM, eNOMSG, eNONET,
              eNOPROTOOPT, eNOSPC, eNOSR, eNOSTR, eNOSYS, eNOTBLK, eNOTCONN,
              eNOTDIR, eNOTEMPTY, eNOTSOCK, eNOTTY, eNXIO, eOPNOTSUPP,
              ePERM, ePFNOSUPPORT, ePIPE, ePROCLIM, ePROCUNAVAIL,
              ePROGMISMATCH, ePROGUNAVAIL, ePROTO, ePROTONOSUPPORT,
              ePROTOTYPE, eRANGE, eREMCHG, eREMOTE, eROFS, eRPCMISMATCH,
              eRREMOTE, eSHUTDOWN, eSOCKTNOSUPPORT, eSPIPE, eSRCH, eSRMNT,
              eSTALE, eTIME, eTIMEDOUT, eTOOMANYREFS, eTXTBSY, eUSERS,
              eWOULDBLOCK, eXDEV, isValidErrno, 
              getErrno, resetErrno, errnoToIOError,
              throwErrno, throwErrnoIf, throwErrnoIf_,
              throwErrnoIfRetry, throwErrnoIfRetry_,
              throwErrnoIfMinus1, throwErrnoIfMinus1_,
              throwErrnoIfMinus1Retry, throwErrnoIfMinus1Retry_,
              throwErrnoIfNull, throwErrnoIfNullRetry) where
import Ptr
import CTypes
import CString
import IO
import Unsafe

newtype Errno = Errno CInt deriving Eq

eOK = Errno 0
foreign import ccall "CError.h" e2BIG :: Errno
foreign import ccall "CError.h" eACCES :: Errno
foreign import ccall "CError.h" eADDRINUSE :: Errno
foreign import ccall "CError.h" eADDRNOTAVAIL :: Errno
foreign import ccall "CError.h" eADV :: Errno
foreign import ccall "CError.h" eAFNOSUPPORT :: Errno
foreign import ccall "CError.h" eAGAIN :: Errno
foreign import ccall "CError.h" eALREADY :: Errno
foreign import ccall "CError.h" eBADF :: Errno
foreign import ccall "CError.h" eBADMSG :: Errno
foreign import ccall "CError.h" eBADRPC :: Errno
foreign import ccall "CError.h" eBUSY :: Errno
foreign import ccall "CError.h" eCHILD :: Errno
foreign import ccall "CError.h" eCOMM :: Errno
foreign import ccall "CError.h" eCONNABORTED :: Errno
foreign import ccall "CError.h" eCONNREFUSED :: Errno
foreign import ccall "CError.h" eCONNRESET :: Errno
foreign import ccall "CError.h" eDEADLK :: Errno
foreign import ccall "CError.h" eDESTADDRREQ :: Errno
foreign import ccall "CError.h" eDIRTY :: Errno
foreign import ccall "CError.h" eDOM :: Errno
foreign import ccall "CError.h" eDQUOT :: Errno
foreign import ccall "CError.h" eEXIST :: Errno
foreign import ccall "CError.h" eFAULT :: Errno
foreign import ccall "CError.h" eFBIG :: Errno
foreign import ccall "CError.h" eFTYPE :: Errno
foreign import ccall "CError.h" eHOSTDOWN :: Errno
foreign import ccall "CError.h" eHOSTUNREACH :: Errno
foreign import ccall "CError.h" eIDRM :: Errno
foreign import ccall "CError.h" eILSEQ :: Errno
foreign import ccall "CError.h" eINPROGRESS :: Errno
foreign import ccall "CError.h" eINTR :: Errno
foreign import ccall "CError.h" eINVAL :: Errno
foreign import ccall "CError.h" eIO :: Errno
foreign import ccall "CError.h" eISCONN :: Errno
foreign import ccall "CError.h" eISDIR :: Errno
foreign import ccall "CError.h" eLOOP :: Errno
foreign import ccall "CError.h" eMFILE :: Errno
foreign import ccall "CError.h" eMLINK :: Errno
foreign import ccall "CError.h" eMSGSIZE :: Errno
foreign import ccall "CError.h" eMULTIHOP :: Errno
foreign import ccall "CError.h" eNAMETOOLONG :: Errno
foreign import ccall "CError.h" eNETDOWN :: Errno
foreign import ccall "CError.h" eNETRESET :: Errno
foreign import ccall "CError.h" eNETUNREACH :: Errno
foreign import ccall "CError.h" eNFILE :: Errno
foreign import ccall "CError.h" eNOBUFS :: Errno
foreign import ccall "CError.h" eNODATA :: Errno
foreign import ccall "CError.h" eNODEV :: Errno
foreign import ccall "CError.h" eNOENT :: Errno
foreign import ccall "CError.h" eNOEXEC :: Errno
foreign import ccall "CError.h" eNOLCK :: Errno
foreign import ccall "CError.h" eNOLINK :: Errno
foreign import ccall "CError.h" eNOMEM :: Errno
foreign import ccall "CError.h" eNOMSG :: Errno
foreign import ccall "CError.h" eNONET :: Errno
foreign import ccall "CError.h" eNOPROTOOPT :: Errno
foreign import ccall "CError.h" eNOSPC :: Errno
foreign import ccall "CError.h" eNOSR :: Errno
foreign import ccall "CError.h" eNOSTR :: Errno
foreign import ccall "CError.h" eNOSYS :: Errno
foreign import ccall "CError.h" eNOTBLK :: Errno
foreign import ccall "CError.h" eNOTCONN :: Errno
foreign import ccall "CError.h" eNOTDIR :: Errno
foreign import ccall "CError.h" eNOTEMPTY :: Errno
foreign import ccall "CError.h" eNOTSOCK :: Errno
foreign import ccall "CError.h" eNOTTY :: Errno
foreign import ccall "CError.h" eNXIO :: Errno
foreign import ccall "CError.h" eOPNOTSUPP :: Errno
foreign import ccall "CError.h" ePERM :: Errno
foreign import ccall "CError.h" ePFNOSUPPORT :: Errno
foreign import ccall "CError.h" ePIPE :: Errno
foreign import ccall "CError.h" ePROCLIM :: Errno
foreign import ccall "CError.h" ePROCUNAVAIL :: Errno
foreign import ccall "CError.h" ePROGMISMATCH :: Errno
foreign import ccall "CError.h" ePROGUNAVAIL :: Errno
foreign import ccall "CError.h" ePROTO :: Errno
foreign import ccall "CError.h" ePROTONOSUPPORT :: Errno
foreign import ccall "CError.h" ePROTOTYPE :: Errno
foreign import ccall "CError.h" eRANGE :: Errno
foreign import ccall "CError.h" eREMCHG :: Errno
foreign import ccall "CError.h" eREMOTE :: Errno
foreign import ccall "CError.h" eROFS :: Errno
foreign import ccall "CError.h" eRPCMISMATCH :: Errno
foreign import ccall "CError.h" eRREMOTE :: Errno
foreign import ccall "CError.h" eSHUTDOWN :: Errno
foreign import ccall "CError.h" eSOCKTNOSUPPORT :: Errno
foreign import ccall "CError.h" eSPIPE :: Errno
foreign import ccall "CError.h" eSRCH :: Errno
foreign import ccall "CError.h" eSRMNT :: Errno
foreign import ccall "CError.h" eSTALE :: Errno
foreign import ccall "CError.h" eTIME :: Errno
foreign import ccall "CError.h" eTIMEDOUT :: Errno
foreign import ccall "CError.h" eTOOMANYREFS :: Errno
foreign import ccall "CError.h" eTXTBSY :: Errno
foreign import ccall "CError.h" eUSERS :: Errno
foreign import ccall "CError.h" eWOULDBLOCK :: Errno
foreign import ccall "CError.h" eXDEV :: Errno

isValidErrno :: Errno -> Bool
isValidErrno (Errno e) = e >= 0

foreign import ccall "errno.h &" errno :: Ptr CInt

getErrno :: IO Errno
getErrno = peekInt errno >>= \e -> return (Errno e)

resetErrno :: IO ()
resetErrno = pokeInt errno 0

errnoToIOError :: String -> Errno -> Maybe Handle -> Maybe String -> IOError
errnoToIOError loc (Errno e) _ _ = if null loc then cs else loc ++ ": " ++ cs
  where foreign import ccall "string.h" strerror :: CInt -> IO CString
        cs = unsafePerformIO (strerror e >>= peekCString)

throwErrno :: String -> IO a
throwErrno loc =
  getErrno >>= \e -> ioError (errnoToIOError loc e Nothing Nothing)

throwErrnoIf :: (a -> Bool) -> String -> IO a -> IO a
throwErrnoIf f loc m = m >>= \x -> if f x then throwErrno loc else return x

throwErrnoIf_ :: (a -> Bool) -> String -> IO a -> IO ()
throwErrnoIf_ f loc m = m >>= \x -> if f x then throwErrno loc else return ()

throwErrnoIfRetry :: (a -> Bool) -> String -> IO a -> IO a
throwErrnoIfRetry f loc m =
  m >>= \x ->
  if f x then
    getErrno >>= \e ->
    if e == eINTR then throwErrnoIfRetry f loc m else throwErrno loc
  else return x

throwErrnoIfRetry_ :: (a -> Bool) -> String -> IO a -> IO ()
throwErrnoIfRetry_ f loc m =
  m >>= \x ->
  if f x then
    getErrno >>= \e ->
    if e == eINTR then throwErrnoIfRetry_ f loc m else throwErrno loc
  else return ()

throwErrnoIfMinus1 :: Num a => String -> IO a -> IO a
throwErrnoIfMinus1 = throwErrnoIf (-1 ==)

throwErrnoIfMinus1_ :: Num a => String -> IO a -> IO ()
throwErrnoIfMinus1_ = throwErrnoIf_ (-1 ==)

throwErrnoIfMinus1Retry :: Num a => String -> IO a -> IO a
throwErrnoIfMinus1Retry = throwErrnoIfRetry (-1 ==)

throwErrnoIfMinus1Retry_ :: Num a => String -> IO a -> IO ()
throwErrnoIfMinus1Retry_ = throwErrnoIfRetry_ (-1 ==)

throwErrnoIfNull :: String -> IO (Ptr a) -> IO (Ptr a)
throwErrnoIfNull = throwErrnoIf (nullPtr ==)

throwErrnoIfNullRetry :: String -> IO (Ptr a) -> IO (Ptr a)
throwErrnoIfNullRetry = throwErrnoIfRetry (nullPtr ==)
