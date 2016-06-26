-- Simple test that importing/exporting of field labels works (see
-- rec011.curry for a variant of this example)

import A(List(), hd,tl, nil,cons,len, Identity(),unId,mkId)

main = print (unId (mkId (len (1 `cons` 2 `cons` 3 `cons` nil))))
