{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RoleAnnotations #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- | A simple abstract type
module CoercibleGenericsAbstract (Abstract) where

data Abstract a = Abstract a
