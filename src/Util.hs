{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
module Util (module ClassyPrelude, type (|->), (!!), (!)) where
import           ClassyPrelude

type (|->) = HashMap


(!!) :: (IsSequence seq) => seq -> Index seq -> Maybe (Element seq)
(!!) = index

(!) :: (IsSequence seq) => seq -> Index seq -> Element seq
(!) = unsafeIndex
