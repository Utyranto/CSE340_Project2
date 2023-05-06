/*
 * Copyright (C) Rida Bazzi, 2017
 *
 * Do not share this file with anyone
 */
#include <iostream>
#include <istream>
#include <vector>
#include <string>
#include <cctype>

#include "lexer.h"
#include "inputbuf.h"

using namespace std;

// Lexer modified for FIRST & FOLLOW project

string reserved[] = { "END_OF_FILE", "ARROW", "STAR", "HASH", "ID", "ERROR" };

void Token::Print()
{
    cout << "{" << this->lexeme << " , "
         << reserved[(int) this->token_type] << " , "
         << this->line_no << "}\n";
}

LexicalAnalyzer::LexicalAnalyzer()
{
    this->line_no = 1;
    tmp.lexeme = "";
    tmp.line_no = 1;
    tmp.token_type = ERROR;

    Token token = GetTokenMain();
    index = 0;

    while (token.token_type != END_OF_FILE)
    {
        tokenList.push_back(token);     // push token into internal list
        token = GetTokenMain();        // and get next token from standatd input
    }
    // pushes END_OF_FILE is not pushed on the token list
}

bool LexicalAnalyzer::SkipSpace()
{
    char c;
    bool space_encountered = false;

    input.GetChar(c);
    line_no += (c == '\n');

    while (!input.EndOfInput() && isspace(c)) {
        space_encountered = true;
        input.GetChar(c);
        line_no += (c == '\n');
    }

    if (!input.EndOfInput()) {
        input.UngetChar(c);
    }
    return space_encountered;
}

Token LexicalAnalyzer::ScanId()
{
    char c;
    input.GetChar(c);

    if (isalpha(c)) {
        tmp.lexeme = "";
        while (!input.EndOfInput() && isalnum(c)) {
            tmp.lexeme += c;
            input.GetChar(c);
        }
        if (!input.EndOfInput()) {
            input.UngetChar(c);
        }
        tmp.line_no = line_no;
        tmp.token_type = ID;
    } else {
        if (!input.EndOfInput()) {
            input.UngetChar(c);
        }
        tmp.lexeme = "";
        tmp.token_type = ERROR;
    }
    return tmp;
}

// GetToken() accesses tokens from the tokenList that is populated when a 
// lexer object is instantiated
Token LexicalAnalyzer::GetToken()
{
    Token token;
    if (index == tokenList.size()){       // return end of file if
        token.lexeme = "";                // index is too large
        token.line_no = line_no;
        token.token_type = END_OF_FILE;
    }
    else{
        token = tokenList[index];
        index = index + 1;
    }
    return token;
}

// peek requires that the argument "howFar" be positive.
Token LexicalAnalyzer::peek(int howFar)
{
    if (howFar <= 0) {      // peeking backward or in place is not allowed
        cout << "LexicalAnalyzer:peek:Error: non positive argument\n";
        exit(-1);
    }

    int peekIndex = index + howFar - 1;
    if (peekIndex > ((int)tokenList.size()-1)) { // if peeking too far
        Token token;                        // return END_OF_FILE
        token.lexeme = "";
        token.line_no = line_no;
        token.token_type = END_OF_FILE;
        return token;
    } else
        return tokenList[peekIndex];
}

Token LexicalAnalyzer::GetTokenMain()
{
    char c;
    
    SkipSpace();
    tmp.lexeme = "";
    tmp.line_no = line_no;
    tmp.token_type = END_OF_FILE;
    if (!input.EndOfInput())
        input.GetChar(c);
    else
        return tmp;
    
    switch (c) {
        case '-':
            input.GetChar(c);
            if (c == '>') {
                tmp.token_type = ARROW;
            } else {
                if (!input.EndOfInput()) {
                    input.UngetChar(c);
                }
                tmp.token_type = ERROR;
            }
            return tmp;
        case '#':
            tmp.token_type = HASH;
            return tmp;
        case '*':
            tmp.token_type = STAR;
            return tmp;
        default:
            if (isalpha(c)) {
                input.UngetChar(c);
                return ScanId();
            } else if (input.EndOfInput())
                tmp.token_type = END_OF_FILE;
            else
                tmp.token_type = ERROR;

            return tmp;
    }
}

