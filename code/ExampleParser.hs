{-# LANGUAGE NoMonomorphismRestriction #-}
module ExampleParser where

import Text.Parsec
import Text.Parsec.Expr
import Data.Char
import qualified Text.Parsec.Token as P

import ExampleLanguage

language_def = P.LanguageDef { 
                               P.commentStart = "/*",
                               P.commentEnd = "*/",
                               P.commentLine = "//",
                               P.nestedComments = True,
                               P.identStart = letter <|> char '_',
                               P.identLetter = letter <|> digit <|> oneOf "_$#",
                               P.opStart = oneOf "+-*:=",
                               P.opLetter = oneOf "=>",
                               P.reservedNames = ["let", "in", "if", "then", "else"],
                               P.reservedOpNames = ["+", "-", "*", "=>", ":=", ";", "(", ")"],
                               P.caseSensitive = True
                             }

lexer = P.makeTokenParser language_def

ws = (\x -> (P.whiteSpace lexer) >> return x)

parens u = P.parens lexer u >>= ws
braces u = P.braces lexer u >>= ws
identifier = P.identifier lexer >>= ws
keyword u = P.reserved lexer u >>= ws
operator u = P.reservedOp lexer u >>= ws
integer = P.integer lexer >>= ws
comma = P.comma lexer >>= ws
semi = P.semi lexer >>= ws

assign_parser = do
                  var <- identifier
                  operator ":="
                  expr <- exp_parser
                  return (EAssign var expr)

if_parser = do
              keyword "if"
              condition <- exp_parser
              keyword "then"
              true_branch <- exp_parser
              keyword "else"
              false_branch <- exp_parser
              return (EIf condition true_branch false_branch)

let_parser = do
              keyword "let"
              variable <- identifier
              operator "="
              expr <- exp_parser
              keyword "in"
              body <- exp_parser
              return (ELet variable expr body)

lambda_parser = do
                  args <- parens (sepBy identifier comma)
                  operator "=>"
                  expr <- exp_parser
                  return (ELambda args expr)

call_parser = do
                  target <- identifier
                  args <- parens (sepBy exp_parser comma)
                  return (ECall (EVar target) args)

term_parser = try (integer >>= (\x -> return (ENum x))) <|>
              try (lambda_parser) <|>
              try (parens exp_parser) <|>
              try call_parser <|>
              try (identifier >>= (\x -> return (EVar x))) <?>
              "could not read term"

binary name func = Infix (do { operator name; return func }) AssocLeft
binop_parser = buildExpressionParser
               [
                 [binary "*" (EBinop Times)],
                 [binary "+" (EBinop Plus), binary "-" (EBinop Minus)]
               ]
               term_parser

exp_parser = try if_parser <|>
               try let_parser <|>
               try assign_parser <|>
               try binop_parser <?>
               "could not read expression"

--exp_parser = (sepBy1 exp_parser semi) >>= (\list -> return (foldl1 (\a -> \b -> ESeq a b) list))

run_parser p input =
  case (parse (p >>= (\x -> eof >> return x)) "" input) of
    Left err -> error ("parse error at " ++ (show err))
    Right x -> x
