{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Record.Beam.DbSettings (
    autoDbSettings
  , autoTblSettings
  , AutoDbSettingsI
  , CheckTblField
  ) where

import Data.Kind
import Data.Record.Generic
import Data.Record.Generic.Transform
import Data.Text (Text)
import Database.Beam.Schema.Tables
import Lens.Micro ((%~))

import qualified Data.Record.Generic.Rep as Rep
import qualified Data.Text               as T

import Data.Record.Beam.Internal

-- | Version of beam's 'defaultDbSettings' for large records
autoDbSettings :: forall be db.
     ( Generic (DatabaseSettings be db)
     , Generic (db Uninterpreted)
     , Constraints (db Uninterpreted) AutoDbSettingsI
     , HasNormalForm (DefaultInterpretation (DatabaseEntity be db)) (DatabaseSettings be db) (db Uninterpreted)
     )
  => DatabaseSettings be db
autoDbSettings =
      to . denormalize1 (Proxy @DefaultInterpretation)
    $ Rep.cmap (Proxy @AutoDbSettingsI) (autoDbSettingsI . T.pack . unK)
    $ recordFieldNames (metadata (Proxy @(db Uninterpreted)))

-- | Version of beam's 'defTblFieldSettings' for large records
--
-- NOTE: If @tbl == tbl'@, then @autoTblSettings :: TableSettings tbl@.
autoTblSettings :: forall tbl tbl'.
     ( Generic (tbl (TableField tbl'))
     , Constraints (tbl (TableField tbl')) CheckTblField
     )
  => tbl (TableField tbl')
autoTblSettings =
      to
    $ Rep.cmap (Proxy @CheckTblField) (mapKI $ tblField . T.pack)
    $ recordFieldNames (metadata (Proxy @(tbl (TableField tbl'))))

{-------------------------------------------------------------------------------
  Internal: cases for 'autoDbSettings'
-------------------------------------------------------------------------------}

class AutoDbSettingsI (a :: Type) where
  autoDbSettingsI :: Text -> Interpret (DefaultInterpretation (DatabaseEntity be db)) a

instance ( -- Required by 'DatabaseEntity'
           Table tbl
           -- Required by 'autoTblSettings'
         , Generic (TableSettings tbl)
         , Constraints (TableSettings tbl) CheckTblField
         ) => AutoDbSettingsI (Uninterpreted (TableEntity tbl)) where
  autoDbSettingsI nm = Interpret $ DatabaseEntity $
      DatabaseTable {
          dbTableSchema      = Nothing
        , dbTableOrigName    = nm
        , dbTableCurrentName = unCamelCaseSel nm
        , dbTableSettings    = autoTblSettings
        }

instance (-- Required by 'DatabaseEntity'
           Beamable tbl
           -- Required by 'autoTblSettings'
         , Generic (TableSettings tbl)
         , Constraints (TableSettings tbl) CheckTblField
         ) => AutoDbSettingsI (Uninterpreted (ViewEntity tbl)) where
  autoDbSettingsI nm = Interpret $ DatabaseEntity
      DatabaseView {
          dbViewSchema      = Nothing
        , dbViewOrigName    = nm
        , dbViewCurrentName = unCamelCaseSel nm
        , dbViewSettings    = autoTblSettings
        }

instance AutoDbSettingsI (Uninterpreted (DomainTypeEntity a)) where
  autoDbSettingsI nm = Interpret $ DatabaseEntity $
      DatabaseDomainType Nothing nm

{-------------------------------------------------------------------------------
  Internal: cases for 'autoTblSettings'

  NOTE: This does /not/ use the @Transform@ infrastructure.
-------------------------------------------------------------------------------}

class CheckTblField a where
  tblField :: T.Text -> a

instance CheckTblField (TableField tbl a) where
  tblField fname = TableField {
        _fieldPath = pure fname
      , _fieldName = unCamelCaseSel fname
      }

instance ( ChooseSubTableStrategy tbl sub ~ strategy
         , SubTableStrategyImpl strategy f sub
         , TagReducesTo f (TableField tbl)
         , Beamable sub
         ) => CheckTblField (sub f) where
  tblField origSelName =
      changeBeamRep (reduceTag %~ nestField) tbl
    where
      tbl :: sub f
      tbl = namedSubTable (Proxy @strategy)

      relName :: T.Text
      relName = unCamelCaseSel origSelName

      nestField :: Columnar' (TableField tbl) a -> Columnar' (TableField tbl) a
      nestField (Columnar' (TableField path nm)) = Columnar' $
          TableField {
                _fieldPath = pure origSelName <> path
              , _fieldName = relName <> "__" <> nm
              }

{-------------------------------------------------------------------------------
  Internal: subcases for constructing table settings for nested tables

  NOTE: While the 'SubTableStrategyImpl' class itself is identical to the one
  in beam, the instances are not.
-------------------------------------------------------------------------------}

class SubTableStrategyImpl (strategy :: SubTableStrategy) (f :: Type -> Type) sub where
  namedSubTable :: Proxy strategy -> sub f

instance ( Generic (sub f)
         , Constraints (sub (TableField tbl)) CheckTblField
         , f ~ TableField tbl
         ) => SubTableStrategyImpl 'BeamableStrategy f sub where
  namedSubTable _ = autoTblSettings

instance ( Generic (rel (TableField rel))
         , Constraints (rel (TableField rel)) CheckTblField
         , TagReducesTo f (TableField tbl)
         , Table rel
         ) => SubTableStrategyImpl 'PrimaryKeyStrategy f (PrimaryKey rel) where
  namedSubTable _ = primaryKey $
      changeBeamRep reduce (autoTblSettings @rel @rel)
    where
      reduce :: Columnar' (TableField rel) a -> Columnar' f a
      reduce (Columnar' (TableField path nm)) = unI $
          reduceTag (\ _ -> pure (Columnar' (TableField path nm))) undefined

instance ( CheckNullable f
         , SubTableStrategyImpl 'PrimaryKeyStrategy f (PrimaryKey rel)
         ) => SubTableStrategyImpl 'RecursiveKeyStrategy f (PrimaryKey rel) where
  namedSubTable _ = namedSubTable (Proxy @'PrimaryKeyStrategy)

