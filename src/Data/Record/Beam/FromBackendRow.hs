{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Data.Record.Beam.FromBackendRow (
    gfromBackendRow
  , gvaluesNeeded
  ) where

import Data.List (foldl')
import Data.Record.Generic
import Database.Beam.Backend.SQL.Row

import qualified Data.Record.Generic.Rep as Rep

-- | Generic implementation of the 'FromBackendRow' 'fromBackendRow' class method
gfromBackendRow :: forall be a.
     ( Generic a
     , Constraints a (FromBackendRow be)
     )
  => FromBackendRowM be a
gfromBackendRow =
    fmap to . Rep.sequenceA $
      Rep.cpure (Proxy @(FromBackendRow be)) $
        Comp (I <$> fromBackendRow)

-- | Generic implementation of the 'FromBackendRow' 'valuesNeeded' class method
gvaluesNeeded :: forall be a.
     ( Generic a
     , Constraints a (FromBackendRow be)
     )
  => Proxy be -> Proxy a -> Int
gvaluesNeeded pBackend _ =
    foldl' (+) 0 $ Rep.collapse values
  where
    values :: Rep (K Int) a
    values = Rep.cpure (Proxy @(FromBackendRow be)) aux

    aux :: forall x. FromBackendRow be x => K Int x
    aux = K $ valuesNeeded pBackend (Proxy @x)

{-
-- BeamBackend instead of BeamSqlBackend to prevent circular super class
class BeamBackend be => FromBackendRow be a where
  -- | Parses a beam row. This should not fail, except in the case of
  -- an internal bug in beam deserialization code. If it does fail,
  -- this should throw a 'BeamRowParseError'.
  fromBackendRow :: FromBackendRowM be a
  default fromBackendRow :: (Typeable a, BackendFromField be a) => FromBackendRowM be a
  fromBackendRow = parseOneField

  valuesNeeded :: Proxy be -> Proxy a -> Int
  valuesNeeded _ _ = 1

instance ( BeamBackend be, Generic (tbl Identity), Generic (tbl Exposed)
         , GFromBackendRow be (Rep (tbl Exposed)) (Rep (tbl Identity))) =>

    FromBackendRow be (tbl Identity) where
  fromBackendRow = to <$> gFromBackendRow (Proxy @(Rep (tbl Exposed)))
  valuesNeeded be _ = gValuesNeeded be (Proxy @(Rep (tbl Exposed))) (Proxy @(Rep (tbl Identity)))

instance ( BeamBackend be, Generic (tbl (Nullable Identity)), Generic (tbl (Nullable Exposed))
         , GFromBackendRow be (Rep (tbl (Nullable Exposed))) (Rep (tbl (Nullable Identity)))) =>

    FromBackendRow be (tbl (Nullable Identity)) where
  fromBackendRow = to <$> gFromBackendRow (Proxy @(Rep (tbl (Nullable Exposed))))
  valuesNeeded be _ = gValuesNeeded be (Proxy @(Rep (tbl (Nullable Exposed)))) (Proxy @(Rep (tbl (Nullable Identity))))


class GFromBackendRow be (exposed :: Type -> Type) rep where
  gFromBackendRow :: Proxy exposed -> FromBackendRowM be (rep ())
  gValuesNeeded :: Proxy be -> Proxy exposed -> Proxy rep -> Int
instance GFromBackendRow be e p => GFromBackendRow be (M1 t f e) (M1 t f p) where
  gFromBackendRow _ = M1 <$> gFromBackendRow (Proxy @e)
  gValuesNeeded be _ _ = gValuesNeeded be (Proxy @e) (Proxy @p)
instance GFromBackendRow be e U1 where
  gFromBackendRow _ = pure U1
  gValuesNeeded _ _ _ = 0
instance (GFromBackendRow be aExp a, GFromBackendRow be bExp b) => GFromBackendRow be (aExp :*: bExp) (a :*: b) where
  gFromBackendRow _ = (:*:) <$> gFromBackendRow (Proxy @aExp) <*> gFromBackendRow (Proxy @bExp)
  gValuesNeeded be _ _ = gValuesNeeded be (Proxy @aExp) (Proxy @a) + gValuesNeeded be (Proxy @bExp) (Proxy @b)

instance FromBackendRow be x => GFromBackendRow be (K1 R (Exposed x)) (K1 R x) where
    gFromBackendRow _ = K1 <$> fromBackendRow
    gValuesNeeded be _ _ = valuesNeeded be (Proxy @x)

instance FromBackendRow be (t Identity) => GFromBackendRow be (K1 R (t Exposed)) (K1 R (t Identity)) where
    gFromBackendRow _ = K1 <$> fromBackendRow
    gValuesNeeded be _ _ = valuesNeeded be (Proxy @(t Identity))

instance FromBackendRow be (t (Nullable Identity)) => GFromBackendRow be (K1 R (t (Nullable Exposed))) (K1 R (t (Nullable Identity))) where
    gFromBackendRow _ = K1 <$> fromBackendRow
    gValuesNeeded be _ _ = valuesNeeded be (Proxy @(t (Nullable Identity)))
-}

