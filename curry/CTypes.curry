-- $Id: CTypes.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module CTypes where
import Ptr
import StablePtr

{- character types -}
type CChar = Char
type CSChar = Char
type CUChar = Char

foreign import ccall "prims.h primSizeOfChar" sizeOfChar :: Int
foreign import ccall "prims.h primSizeOfChar" sizeOfSChar :: Int
foreign import ccall "prims.h primSizeOfChar" sizeOfUChar :: Int

foreign import ccall "prims.h primAlignmentChar" alignmentChar :: Int
foreign import ccall "prims.h primAlignmentChar" alignmentSChar :: Int
foreign import ccall "prims.h primAlignmentChar" alignmentUChar :: Int

foreign import ccall "prims.h primPeekChar"
        peekChar :: Ptr CChar -> IO CChar
foreign import ccall "prims.h primPeekSChar"
        peekSChar :: Ptr CSChar -> IO CSChar
foreign import ccall "prims.h primPeekUChar"
        peekUChar :: Ptr CUChar -> IO CUChar

foreign import ccall "prims.h primPokeChar"
        pokeChar :: Ptr CChar -> CChar -> IO ()
foreign import ccall "prims.h primPokeSChar"
        pokeSChar :: Ptr CSChar -> CSChar -> IO ()
foreign import ccall "prims.h primPokeUChar"
        pokeUChar :: Ptr CUChar -> CUChar -> IO ()

{- integer types -}
type CShort = Int
type CUShort = Int
type CInt = Int
type CUInt = Int
type CLong = Int
type CULong = Int

foreign import ccall "prims.h primSizeOfShort" sizeOfShort :: Int
foreign import ccall "prims.h primSizeOfShort" sizeOfUShort :: Int
foreign import ccall "prims.h primSizeOfInt" sizeOfInt :: Int
foreign import ccall "prims.h primSizeOfInt" sizeOfUInt :: Int
foreign import ccall "prims.h primSizeOfLong" sizeOfLong :: Int
foreign import ccall "prims.h primSizeOfLong" sizeOfULong :: Int

foreign import ccall "prims.h primAlignmentShort" alignmentShort :: Int
foreign import ccall "prims.h primAlignmentShort" alignmentUShort :: Int
foreign import ccall "prims.h primAlignmentInt" alignmentInt :: Int
foreign import ccall "prims.h primAlignmentInt" alignmentUInt :: Int
foreign import ccall "prims.h primAlignmentLong" alignmentLong :: Int
foreign import ccall "prims.h primAlignmentLong" alignmentULong :: Int

foreign import ccall "prims.h primPeekShort"
        peekShort :: Ptr CShort -> IO CShort
foreign import ccall "prims.h primPeekUShort"
        peekUShort :: Ptr CUShort -> IO CUShort
foreign import ccall "prims.h primPeekInt"
        peekInt :: Ptr CInt -> IO CInt
foreign import ccall "prims.h primPeekUInt"
        peekUInt :: Ptr CUInt -> IO CUInt
foreign import ccall "prims.h primPeekLong"
        peekLong :: Ptr CLong -> IO CLong
foreign import ccall "prims.h primPeekULong"
        peekULong :: Ptr CULong -> IO CULong

foreign import ccall "prims.h primPokeShort"
        pokeShort :: Ptr CShort -> CShort -> IO ()
foreign import ccall "prims.h primPokeUShort"
        pokeUShort :: Ptr CUShort -> CUShort -> IO ()
foreign import ccall "prims.h primPokeInt"
        pokeInt :: Ptr CInt -> CInt -> IO ()
foreign import ccall "prims.h primPokeUInt"
        pokeUInt :: Ptr CUInt -> CUInt -> IO ()
foreign import ccall "prims.h primPokeLong"
        pokeLong :: Ptr CLong -> CLong -> IO ()
foreign import ccall "prims.h primPokeULong"
        pokeULong :: Ptr CULong -> CULong -> IO ()

{- floating point types -}
type CFloat = Float
type CDouble = Float

foreign import ccall "prims.h primSizeOfFloat" sizeOfFloat :: Int
foreign import ccall "prims.h primSizeOfDouble" sizeOfDouble :: Int

foreign import ccall "prims.h primAlignmentFloat" alignmentFloat :: Int
foreign import ccall "prims.h primAlignmentDouble" alignmentDouble :: Int

foreign import ccall "prims.h primPeekFloat"
        peekFloat :: Ptr CFloat -> IO CFloat
foreign import ccall "prims.h primPeekDouble"
        peekDouble :: Ptr CDouble -> IO CDouble

foreign import ccall "prims.h primPokeFloat"
        pokeFloat :: Ptr CFloat -> CFloat -> IO ()
foreign import ccall "prims.h primPokeDouble"
        pokeDouble :: Ptr CDouble -> CDouble -> IO ()

{- pointer types -}
foreign import ccall "prims.h primSizeOfPtr" sizeOfPtr :: Int
foreign import ccall "prims.h primSizeOfFunPtr" sizeOfFunPtr :: Int
foreign import ccall "prims.h primSizeOfPtr" sizeOfStablePtr :: Int

foreign import ccall "prims.h primAlignmentPtr" alignmentPtr :: Int
foreign import ccall "prims.h primAlignmentFunPtr" alignmentFunPtr :: Int
foreign import ccall "prims.h primAlignmentPtr" alignmentStablePtr :: Int

foreign import ccall "prims.h primPeekPtr"
        peekPtr :: Ptr (Ptr a) -> IO (Ptr a)
foreign import ccall "prims.h primPeekFunPtr"
        peekFunPtr :: Ptr (FunPtr a) -> IO (FunPtr a)
foreign import ccall "prims.h primPeekPtr"
        peekStablePtr :: Ptr (StablePtr a) -> IO (StablePtr a)

foreign import ccall "prims.h primPokePtr"
        pokePtr :: Ptr (Ptr a) -> Ptr a -> IO ()
foreign import ccall "prims.h primPokePtr"
        pokeFunPtr :: Ptr (FunPtr a) -> FunPtr a -> IO ()
foreign import ccall "prims.h primPokeFunPtr"
        pokeStablePtr :: Ptr (StablePtr a) -> StablePtr a -> IO ()
