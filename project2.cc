/*
 * Copyright (C) Mohsen Zohrevandi, 2017
 *               Rida Bazzi 2019
 * Do not share this file with anyone
 */
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <string>
#include <unordered_set>
#include <unordered_map>
#include "lexer.h"

struct rule {
    std::string left;
    std::vector<std::string> right;
};

class Grammar{
    public:
        Grammar();
        std::vector<rule> rule_list;
        std::unordered_set<std::string> nonTerminals;
        std::unordered_set<std::string> terminals;
        std::vector<std::string> allSymbols;
    private:
        LexicalAnalyzer* lexer;
        void parse_input();
        void parse_Grammar();
        void parse_Rule_list();
        void parse_Id_list();
        void parse_Rule();
        void parse_Right_hand_side();
        void syntax_error();
        Token expect(TokenType token);
};

Grammar* gram; //global variable to store the grammar

Grammar::Grammar()
{
    lexer = new LexicalAnalyzer();
    parse_input();
}

// read grammar
void ReadGrammar()
{
    gram = new Grammar();
}

void Grammar::parse_input()
{
    parse_Grammar();
    expect(END_OF_FILE);
}

void Grammar::syntax_error() {
    std::cout << "SYNTAX ERROR !!!\n";
    exit(1);
}

void Grammar::parse_Grammar(){
    parse_Rule_list();
    expect(HASH);
}

void Grammar::parse_Rule_list(){
    parse_Rule();
    Token t = lexer->peek(1);
    if(t.token_type == HASH){
        return; //stop parsing RULE_LIST
    } else {
        parse_Rule_list(); //recurse until HASH is detected.
    }
}

void Grammar::parse_Id_list(){
    Token t = expect(ID);
    
    rule_list[rule_list.size() - 1].right.push_back(t.lexeme); //push to right hand side of the last rule

    // add it to the allSymbols list if we've never seen it before
    if (!nonTerminals.count(t.lexeme) && !terminals.count(t.lexeme)) {
        allSymbols.push_back(t.lexeme);
        terminals.insert(t.lexeme);
    }

    Token y = lexer->peek(1);
    if(y.token_type == STAR){
        return; //stop if there are no more ID Lists.
    } else {
        parse_Id_list(); //recurse.
    }
}

void Grammar::parse_Rule(){

    // As we parse this rule, we should add it to rule_list.

    Token t = expect(ID);
    
    rule newRule;
    newRule.left = t.lexeme;
    if(terminals.count(t.lexeme)){ //if we wrongly classify a symbol as a terminal when it is not, remove it from terminals and add to non-terminals
        terminals.erase(t.lexeme);
        nonTerminals.insert(t.lexeme);
    }
    // add it to the allSymbols list and non-terminals list if we've never seen it before
    if (!nonTerminals.count(t.lexeme) && !terminals.count(t.lexeme)) {
        allSymbols.push_back(t.lexeme);
        nonTerminals.insert(t.lexeme);
    }

    //adds new rule to rule list.
    rule_list.push_back(newRule); 

    expect(ARROW);

    parse_Right_hand_side();

    expect(STAR);

}

void Grammar::parse_Right_hand_side(){
    Token t = lexer->peek(1);
    if(t.token_type == STAR){
        return;
    } else {
        parse_Id_list(); //parse ID List if it's not a STAR
    }
}

Token Grammar::expect(TokenType token){
    Token tok = lexer->GetToken();
    if(tok.token_type == token){
        return tok;
    } else {
        syntax_error();
    }
}

// Task 1
void printTerminalsAndNoneTerminals()
{
    for(int i = 0; i < gram->allSymbols.size(); i++){ //print terminals
        if(gram->terminals.count(gram->allSymbols[i])){
           std::cout << gram->allSymbols[i] + " ";
        }
    }

    for(int j = 0; j < gram->allSymbols.size(); j++){ //print non-terminals
        if(gram->nonTerminals.count(gram->allSymbols[j])){
            std::cout << gram->allSymbols[j] + " ";
        }
    }
}

// Task 2
void RemoveUselessSymbols()
{
    std::unordered_map<std::string, bool> generatingSymbols; //create a map to check for generating symbols
    std::unordered_set<std::string> terminals = gram->terminals;
    std::unordered_set<std::string> nonTerminals = gram->nonTerminals;
    std::vector<rule> rule_list = gram->rule_list;

    // "#" to represent epsilon
    generatingSymbols["#"] = true;

    for (auto it = terminals.begin(); it != terminals.end(); ++it) { //all terminals are generating
        generatingSymbols[*it] = true;
    }

    for(auto jt = nonTerminals.begin(); jt != nonTerminals.end(); ++jt){ //set all non terminals to false for now.
        generatingSymbols[*jt] = false;
    }

    bool change = true;
    while (change) {
        change = false;
        for (int i = 0; i < rule_list.size(); i++){
            rule currentRule = rule_list[i];
            bool ruleIsGenerating = true;
            for (int j = 0; j < currentRule.right.size(); j++){
                if(!generatingSymbols[currentRule.right[j]]){
                    ruleIsGenerating = false;
                    break;
                }
            } 
            if(ruleIsGenerating && !generatingSymbols[currentRule.left]){ //sets it only once
                generatingSymbols[currentRule.left] = true;
                change = true;
            }
        }
    }

    std::vector<rule> RulesGen; //new vector
    for(int i = 0; i < rule_list.size(); i++){
        if(!generatingSymbols[rule_list[i].left]) {
            continue;
        }
        
        bool rightGen = true;

        for(int j = 0; j < rule_list[i].right.size(); j++){
            if(!generatingSymbols[rule_list[i].right[j]]){
                rightGen = false;
                break;
            }
        }

        if(rightGen){
            RulesGen.push_back(rule_list[i]);
        }
    }

    std::unordered_map<std::string, bool> reachableSymbols;

    //set all terminals to not reachable for now
    for (auto it = terminals.begin(); it != terminals.end(); ++it) {
        reachableSymbols[*it] = false;
    }
    
    //set all non terminals to false for now
    for(auto jt = nonTerminals.begin(); jt != nonTerminals.end(); ++jt){
        reachableSymbols[*jt] = false;
    }

    // if its the start symbol, set it to true.
    reachableSymbols[rule_list[0].left] = true; 

    change = true;
    while(change){
        change = false;
        for(int i = 0; i < RulesGen.size(); i++){
            rule currentRule = RulesGen[i];
            if(reachableSymbols[currentRule.left]) {
                for(int j = 0; j < RulesGen[i].right.size(); j++){
                    if(!reachableSymbols[currentRule.right[j]]) //set to true if we haven't already
                    {
                        reachableSymbols[currentRule.right[j]] = true;
                        change = true;
                    }
                }
            }
        }
    }

    std::vector<rule> usefulRules;

    for(int i = 0; i < RulesGen.size(); i++){
        if(!reachableSymbols[RulesGen[i].left]){
            continue;
        }

        bool rightReach = true;

        for(int j = 0; j < RulesGen[i].right.size(); j++){
            if(!reachableSymbols[RulesGen[i].right[j]]){
                rightReach = false;
                break;
            }
        }

        if(rightReach){
            usefulRules.push_back(RulesGen[i]);
        }
    }

    for(int i = 0; i < usefulRules.size(); i++){
        std::cout << usefulRules[i].left + " -> ";
        if(usefulRules[i].right.empty()){
            std::cout << "#";
        } else {
            for (int j = 0; j < usefulRules[i].right.size(); j++){
                std::cout << usefulRules[i].right[j];
                if (j != usefulRules[i].right.size()-1){
                    std::cout << " ";
                }
            }
        }
        std::cout << "\n";
    }

}

std::unordered_map<std::string, std::unordered_set<std::string>> FirstSetAlgo(){
    std::unordered_map<std::string, std::unordered_set<std::string>> firstSets; //map of first sets
    std::unordered_set<std::string> terminals = gram->terminals;
    std::unordered_set<std::string> nonTerminals = gram->nonTerminals;
    std::vector<rule> ruleList = gram->rule_list;

    for(auto jt = nonTerminals.begin(); jt != nonTerminals.end(); ++jt){
        firstSets[*jt] = {}; //set first sets of nonterminals as empty.
    }

    for(auto it = terminals.begin(); it != terminals.end(); ++it){
        firstSets[*it] = {*it};
    }
    
    bool changed = true;
    while(changed){ //loop until something is changed
        changed = false;
        for(int i = 0; i < ruleList.size(); i++){ 

            // A -> B

            int initialSize = firstSets[ruleList[i].left].size();

            if(ruleList[i].right.empty()){ //check if RHS is empty
                firstSets[ruleList[i].left].insert("#"); //add epsilon in first of RHS
            }
            else{
                for (int j = 0; j < ruleList[i].right.size(); j++) { //loop through all symbols in RHS
                    if(terminals.count(ruleList[i].right[j])){
                        firstSets[ruleList[i].left].insert(ruleList[i].right[j]); //add first of that terminal to first set of LHS
                        break;
                    } else {
                        bool hasEpsilon = false;
                        for(auto iter = firstSets[ruleList[i].right[j]].begin(); iter != firstSets[ruleList[i].right[j]].end(); ++iter){ //rule 3
                            // insert as long as it's not epsilon
                            if (*iter != "#") {
                                firstSets[ruleList[i].left].insert(*iter);
                            } else {
                                hasEpsilon = true;
                            }
                        }

                        if (!hasEpsilon) { //rule 4
                            break;
                        } else {
                            if(j == ruleList[i].right.size() - 1){
                                firstSets[ruleList[i].left].insert("#"); //rule 5
                            }
                            continue;
                        }
                    }
                }
            }
            int finalSize = firstSets[ruleList[i].left].size();
            if (finalSize != initialSize){
                changed = true;
            }
        }
    }
    return firstSets;
}

// Task 3
void CalculateFirstSets()
{
    std::unordered_map<std::string, std::unordered_set<std::string>> firstSets = FirstSetAlgo(); //map of first sets
    std::unordered_set<std::string> terminals = gram->terminals;
    std::unordered_set<std::string> nonTerminals = gram->nonTerminals;
    std::vector<rule> ruleList = gram->rule_list;

    std::vector<std::string> allSymbols = gram->allSymbols;

    for(int i = 0; i < allSymbols.size(); i++){
        if(nonTerminals.count(allSymbols[i])) {
            std::cout << "FIRST(" + allSymbols[i] + ") = ";
            std::string stringToPrint = "{ ";
            if(!firstSets[allSymbols[i]].empty()){
            
                if(firstSets[allSymbols[i]].count("#")){
                    stringToPrint += "#, ";
                }

                for(int j = 0; j < allSymbols.size(); j++){
                    if(firstSets[allSymbols[i]].count(allSymbols[j])){
                        stringToPrint += allSymbols[j] + ", ";
                    }
                }

                stringToPrint = stringToPrint.substr(0, stringToPrint.length()-2);
            }

            stringToPrint += " }";

            std::cout << stringToPrint + '\n';

        }
        
    }

}

// Task 4
void CalculateFollowSets()
{
   
    std::unordered_map<std::string, std::unordered_set<std::string>> firstSets = FirstSetAlgo(); //map of first sets
    
    std::unordered_map<std::string, std::unordered_set<std::string>> followSets;
    std::unordered_set<std::string> terminals = gram->terminals;
    std::unordered_set<std::string> nonTerminals = gram->nonTerminals;
    std::vector<std::string> allSymbols = gram->allSymbols;
    std::vector<rule> ruleList = gram->rule_list;

    

    for(auto it = nonTerminals.begin(); it != nonTerminals.end(); ++it){
        followSets[*it] = {}; //sets all nonterminals as empty for now
    }
    
    followSets[ruleList[0].left] = { "$" }; //set FOLLOW of first rule as $

    bool changed = true;
    while(changed){
        changed = false;
        for(int i = 0; i < ruleList.size(); i++){ //loop through all rules
            for(int j = ruleList[i].right.size() - 1; j >= 0; j--){
                if(nonTerminals.count(ruleList[i].right[j])){
                    int initialSize = followSets[ruleList[i].right[j]].size();
                    
                    for (auto it = followSets[ruleList[i].left].begin(); it != followSets[ruleList[i].left].end(); ++it){
                        followSets[ruleList[i].right[j]].insert(*it); //create array of follow sets of LHS. Loop through array and add symbols in Follow set of current RHS
                    }

                    int finalSize = followSets[ruleList[i].right[j]].size();

                    if(initialSize != finalSize){
                        changed = true;
                    }
                    
                }

                if(firstSets[ruleList[i].right[j]].count("#")){
                    continue;
                } else {
                    break;
                }
            }
            for(int k = 0; k < ruleList[i].right.size(); k++){
                if(!nonTerminals.count(ruleList[i].right[k])){
                    continue;
                } else {
                    for(int l = k + 1; l < ruleList[i].right.size(); l++){
                        
                        int initialSize = followSets[ruleList[i].right[k]].size();
                        bool epsilonPresent = false;
                        // add everything in the first set of the symbol at l 
                        // into the follow set of the symbol at k
                        std::unordered_set<std::string> firstSetofL = firstSets[ruleList[i].right[l]];
                        for(auto it = firstSetofL.begin(); it != firstSetofL.end(); ++it){
                            if(*it != "#"){
                                followSets[ruleList[i].right[k]].insert(*it);
                            } else {
                                epsilonPresent = true;
                            }
                        }
                        
                        int finalSize = followSets[ruleList[i].right[k]].size();

                        if(initialSize != finalSize){
                            changed = true;
                        }

                        if(!epsilonPresent){
                            break;
                        }
                    }
                }
            }
            
        }
    }

    for(int i = 0; i < allSymbols.size(); i++){
        if(nonTerminals.count(allSymbols[i])) {
            std::cout << "FOLLOW(" + allSymbols[i] + ") = ";
            std::string stringToPrint = "{ ";
            if(!followSets[allSymbols[i]].empty()){
            
                if(followSets[allSymbols[i]].count("$")){
                    stringToPrint += "$, ";
                }

                for(int j = 0; j < allSymbols.size(); j++){
                    if(followSets[allSymbols[i]].count(allSymbols[j])){
                        stringToPrint += allSymbols[j] + ", ";
                    }
                }

                stringToPrint = stringToPrint.substr(0, stringToPrint.length()-2);
            }

            stringToPrint += " }";

            std::cout << stringToPrint + '\n';

        }
        
    }
    
}

// Task 5
void CheckIfGrammarHasPredictiveParser()
{
    
}

int main (int argc, char* argv[])
{
    int task;

    if (argc < 2)
    {
        std::cout << "Error: missing argument\n";
        return 1;
    }

    /*
       Note that by convention argv[0] is the name of your executable,
       and the first argument to your program is stored in argv[1]
     */

    task = atoi(argv[1]);
    
    ReadGrammar();  // Reads the input grammar from standard input
                    // and represent it internally in data structures
                    // ad described in project 2 presentation file

    switch (task) {
        case 1: printTerminalsAndNoneTerminals();
            break;

        case 2: RemoveUselessSymbols();
            break;

        case 3: CalculateFirstSets();
            break;

        case 4: CalculateFollowSets();
            break;

        case 5: CheckIfGrammarHasPredictiveParser();
            break;

        default:
            std::cout << "Error: unrecognized task number " << task << "\n";
            break;
    }
    return 0;
}



