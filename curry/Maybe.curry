module Maybe(module Maybe, Maybe(Nothing,Just), maybe) where

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing  = False

isNothing :: Maybe a -> Bool
isNothing (Just _) = False
isNothing Nothing  = True

fromJust :: Maybe a -> a
fromJust (Just x) = x

fromMaybe :: a -> Maybe a -> a
fromMaybe z Nothing  = z
fromMaybe _ (Just x) = x

listToMaybe :: [a] -> Maybe a
listToMaybe []	  = Nothing
listToMaybe (x:_) = Just x

maybeToList :: Maybe a -> [a]
maybeToList Nothing  = []
maybeToList (Just x) = [x]

catMaybes :: [Maybe a] -> [a]
catMaybes xs = [x | Just x <- xs]

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f xs = catMaybes (map f xs)
