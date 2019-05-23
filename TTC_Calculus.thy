theory TTC_Calculus
  imports Main 
         "HOL-Library.Char_ord" 

begin

datatype PLTL_formula =
  F 
| T 
| Var string ("(V _)" [80] 80)
| Not PLTL_formula ("(.\<not> _)" [80] 80)
| And  PLTL_formula  PLTL_formula (infixl ".\<and>" 75)
| Or PLTL_formula  PLTL_formula (infixl ".\<or>" 73)
| Imp PLTL_formula  PLTL_formula (infixr ".\<longrightarrow>" 70)
| X PLTL_formula ("(\<circle> _)" [80] 80)
| U PLTL_formula  PLTL_formula (infixr "\<U>" 72)
| R PLTL_formula  PLTL_formula (infixr "\<R>" 72)
| Alw PLTL_formula ("(\<box> _)" [80] 80)
| Evt PLTL_formula ("(\<diamond> _)" [80] 80)
(* Selected Next and Until, Extra-logic connectives for marking *)
| SelX PLTL_formula ("(\<dieresis>\<circle>\<dieresis> _)" [80] 80)
| SelU PLTL_formula  PLTL_formula (infixr "\<dieresis>\<U>\<dieresis>" 72)  (* Selected Until *)

(* Negation normal form *)

fun notInNNF  :: "PLTL_formula \<Rightarrow> PLTL_formula" ("\<sim>nnf")  where
  "\<sim>nnf F = T" | 
  "\<sim>nnf T = F" | 
  "\<sim>nnf(V x) = (.\<not>(V x))" | 
  "\<sim>nnf(.\<not> phi) =  phi" |
  "\<sim>nnf(phi .\<and> psi) = ((\<sim>nnf phi) .\<or> (\<sim>nnf psi))" |
  "\<sim>nnf(phi .\<or> psi) = ((\<sim>nnf phi) .\<and> (\<sim>nnf psi))" |   
  "\<sim>nnf(phi .\<longrightarrow> psi) = ( phi .\<and> (\<sim>nnf psi))" |
  "\<sim>nnf(\<circle> phi) = \<circle>(\<sim>nnf phi)" |
  "\<sim>nnf(\<dieresis>\<circle>\<dieresis> phi) = \<dieresis>\<circle>\<dieresis>(\<sim>nnf phi)" |
  "\<sim>nnf(phi \<U> psi) = (\<sim>nnf phi) \<R> (\<sim>nnf psi)" | 
  "\<sim>nnf(phi \<dieresis>\<U>\<dieresis> psi) = (\<sim>nnf phi) \<R> (\<sim>nnf psi)" |
  "\<sim>nnf(phi \<R> psi) = (\<sim>nnf phi) \<U> (\<sim>nnf psi)" |
  "\<sim>nnf(\<box> phi) = \<diamond> (\<sim>nnf phi)" |
  "\<sim>nnf(\<diamond> phi) = \<box> (\<sim>nnf phi)"

(* Order on formulas *)

fun  string_leqB :: "string \<Rightarrow> string \<Rightarrow> bool" where
 "string_leqB s r = ord.lexordp_eq (\<lambda>c d. of_char c < (of_char d :: nat)) s r"


fun LessThan_PLTL_Form :: "PLTL_formula \<Rightarrow> PLTL_formula \<Rightarrow> bool" (infix "\<sqsubseteq>" 90)
where
  "F \<sqsubseteq> _ = True"                                     
| "T \<sqsubseteq> beta = (beta \<noteq> F)"                           
| "(V s) \<sqsubseteq> beta = (case beta of                    
                    (V r) \<Rightarrow>  string_leqB s r |
                    F \<Rightarrow> False | T \<Rightarrow> False |  _ \<Rightarrow> True)"    
| "(.\<not> phi) \<sqsubseteq> beta = (case beta of
                       T  \<Rightarrow> False | F  \<Rightarrow> False 
                     | (.\<not> psi) \<Rightarrow> (phi \<sqsubseteq> psi)
                     |  _ \<Rightarrow> True)"  
| "(\<dieresis>\<circle>\<dieresis> phi) \<sqsubseteq> beta  = (case beta of
                        T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False 
                      | (\<dieresis>\<circle>\<dieresis> psi) \<Rightarrow>  ( phi \<sqsubseteq> psi ) 
                      | _ \<Rightarrow> True)"
| "(\<circle> phi) \<sqsubseteq> beta  = (case beta of
                        T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False 
                      | (\<circle> psi) \<Rightarrow>  ( phi \<sqsubseteq> psi ) 
                      | _ \<Rightarrow> True)"
| "(\<box> phi) \<sqsubseteq> beta = (case beta of
                           T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False |  (\<circle> _) \<Rightarrow> False
                          | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False 
                          | (\<box> psi) \<Rightarrow> (phi \<sqsubseteq> psi) 
                          | _ \<Rightarrow> True )"
| "(phi \<R> psi) \<sqsubseteq> beta = (case beta of
                           T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False |  (\<circle> _) \<Rightarrow> False 
                           | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False | (\<box> _) \<Rightarrow> False 
                          | (phi' \<R> psi') \<Rightarrow> (phi \<sqsubseteq> phi') \<or> (phi = phi' \<and> psi \<sqsubseteq> psi')
                          | _ \<Rightarrow> True )"
| "(phi .\<and> psi) \<sqsubseteq> beta = (case beta of
                           T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False |  (\<circle> _) \<Rightarrow> False
                           | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False | (\<box> _) \<Rightarrow> False  |  (_ \<R> _) \<Rightarrow> False 
                          | (phi'.\<and> psi') \<Rightarrow>  (phi \<sqsubseteq> phi') \<or> ((phi = phi') \<and> (psi \<sqsubseteq> psi'))
                          | _ \<Rightarrow> True )" 
| "(phi .\<or> psi) \<sqsubseteq> beta = (case beta of
                           T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False |  (\<circle> _) \<Rightarrow> False 
                          | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False | (\<box> _) \<Rightarrow> False  |  (_ \<R> _) \<Rightarrow> False 
                          |  (_ .\<and> _) \<Rightarrow> False
                          | (phi' .\<or> psi') \<Rightarrow>  (phi \<sqsubseteq> phi') \<or> ((phi = phi') \<and> (psi \<sqsubseteq> psi'))
                          | _ \<Rightarrow> True )"
| "(phi .\<longrightarrow> psi) \<sqsubseteq> beta = (case beta of
                           T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False |  (\<circle> _) \<Rightarrow> False 
                           | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False | (\<box> _) \<Rightarrow> False  |  (_ \<R> _) \<Rightarrow> False
                          |  (_ .\<and> _) \<Rightarrow> False |  (_ .\<or> _) \<Rightarrow> False 
                          | (phi' .\<longrightarrow> psi') \<Rightarrow> (phi \<sqsubseteq> phi') \<or> ((phi = phi') \<and> (psi \<sqsubseteq> psi'))
                          | _ \<Rightarrow> True )"
| "(\<diamond> phi) \<sqsubseteq> beta = (case beta of
                           T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False |  (\<circle> _) \<Rightarrow> False 
                          | (_ .\<and> _) \<Rightarrow> False |  (_ .\<or> _) \<Rightarrow> False |  (_ .\<longrightarrow> _) \<Rightarrow> False 
                          | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False | (\<box> _) \<Rightarrow> False  |  (_ \<R> _) \<Rightarrow> False
                          | (\<diamond> psi) \<Rightarrow> (phi \<sqsubseteq> psi) 
                          | _ \<Rightarrow> True )"
| "(phi \<U> psi) \<sqsubseteq> beta = (case beta of
                           T  \<Rightarrow> False | F  \<Rightarrow> False | (.\<not> _) \<Rightarrow> False |  (\<circle> _) \<Rightarrow> False 
                          | (_ .\<and> _) \<Rightarrow> False |  (_ .\<or> _) \<Rightarrow> False  |  (_ .\<longrightarrow> _) \<Rightarrow> False 
                          | (\<dieresis>\<circle>\<dieresis> _) \<Rightarrow> False | (\<box> _) \<Rightarrow> False | (\<diamond> _) \<Rightarrow> False 
                          | (phi' \<U> psi') \<Rightarrow> (phi \<sqsubseteq> phi') \<or> (phi = phi' \<and> psi \<sqsubseteq> psi')
                          | _ \<Rightarrow> True )"
| "(phi \<dieresis>\<U>\<dieresis> psi) \<sqsubseteq> beta = (case beta of 
                          (phi' \<U> psi') \<Rightarrow> (phi \<sqsubseteq> phi') \<or> (phi = phi' \<and> psi \<sqsubseteq> psi')
                          | _ \<Rightarrow> False )"

(* Sorting lists of formulas *)

fun insert :: "PLTL_formula \<Rightarrow> PLTL_formula list \<Rightarrow> PLTL_formula list"  (infixr "\<bullet>" 85) where
"alpha \<bullet> []  = [alpha]" |
"alpha \<bullet> (h # t) = (if alpha = h then h # t 
                          else if alpha \<sqsubseteq> h then h # (alpha \<bullet> t)
                          else alpha # h # t)"

fun sort :: "PLTL_formula list \<Rightarrow> PLTL_formula list" where
"sort [] = []" |
"sort (h # t) = insert h (sort t)"

(* Unnext function *)

fun isX :: "PLTL_formula \<Rightarrow> bool" where 
"isX (\<circle> _) = True" |
"isX (\<dieresis>\<circle>\<dieresis> _) = True" |
"isX _ = False"    

fun removeX :: "PLTL_formula \<Rightarrow> PLTL_formula" where 
"removeX (\<circle> phi) = phi" |
"removeX (\<dieresis>\<circle>\<dieresis> phi) = phi" |
"removeX  phi = phi"

fun next_state :: "PLTL_formula list \<Rightarrow> PLTL_formula list"  where 
"next_state xs = map removeX (filter isX xs)" 

(* Negated context *)

fun isAlw :: "PLTL_formula \<Rightarrow> bool" where 
"isAlw (\<box> _) = True" |
"isAlw _ = False" 

fun myf :: "PLTL_formula \<Rightarrow>  PLTL_formula \<Rightarrow> PLTL_formula" where
"myf phi F = \<sim>nnf phi" |
"myf phi psi = ((\<sim>nnf phi) .\<or> psi)"

fun disjNeg :: "PLTL_formula list \<Rightarrow> PLTL_formula"  where
"disjNeg [] = F" |
"disjNeg [h] = (\<sim>nnf h)" |
"disjNeg (h#t) =  (disjNeg t) .\<or> (\<sim>nnf h)"

fun negCtxt :: "PLTL_formula list \<Rightarrow> PLTL_formula"  where
"negCtxt [] = F" |
"negCtxt \<Delta> = disjNeg (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Delta>)"

(* Our infix version of ListMem *)

fun inlist :: "PLTL_formula \<Rightarrow> PLTL_formula list \<Rightarrow> bool" (infix ".\<in>" 85) where
"_ .\<in> [] = False" |
"x .\<in> (h # t) = ((x = h) \<or> (x .\<in> t))"

(* Conjunction with subsumption for the negated context*)

fun disj2set:: "PLTL_formula \<Rightarrow> PLTL_formula set" where
(* phi is a disjunctions (with at least a disjunct *)
"disj2set (alpha .\<or> beta) = (disj2set alpha) \<union> (disj2set beta)" |
"disj2set beta = Set.insert beta Set.empty"

fun conj2setOfsets :: "PLTL_formula \<Rightarrow> (PLTL_formula set) set" where
(* phi is a conjunction of disjunctions (at least one) *)
"conj2setOfsets (alpha .\<and> beta) = (conj2setOfsets alpha) \<union> (conj2setOfsets beta)" |
"conj2setOfsets beta =  (Set.insert (disj2set beta) Set.empty)"

fun conjWithSubsumption :: "PLTL_formula \<Rightarrow> PLTL_formula \<Rightarrow>  PLTL_formula" (infix ".\<sqinter>." 85) where
(* phi is a conjunction of disjunctions (at least one) and psi is a disjunction*)
"phi .\<sqinter>. psi = (if Bex (conj2setOfsets phi) (\<lambda>S. S \<le> (disj2set psi))  then phi 
                else phi .\<and> psi)"

(* The TTC_Calculus *)

inductive TTC_proves:: "PLTL_formula list \<Rightarrow> PLTL_formula \<Rightarrow> bool" (infix "\<turnstile>" 50)
  where
(* Contradiction Rules *)
TTC_Ctd1: " ( phi .\<in> \<Delta> \<and> (\<sim>nnf phi) .\<in> \<Delta> )  \<Longrightarrow>  \<Delta> \<turnstile> F" |
TTC_Ctd2: "F .\<in> \<Delta>  \<Longrightarrow>  \<Delta> \<turnstile> F" |
(* Connective Rules *)
TTC_T : "\<Delta> \<turnstile> F \<Longrightarrow> T # \<Delta> \<turnstile> F" |
TTC_And : "phi \<bullet> psi \<bullet> \<Delta>  \<turnstile> F  
           \<Longrightarrow> (phi .\<and> psi) # \<Delta> \<turnstile> F"  |
TTC_Or : "phi \<bullet> \<Delta> \<turnstile> F \<Longrightarrow>  psi \<bullet> \<Delta> \<turnstile> F 
          \<Longrightarrow> (phi .\<or> psi) # \<Delta> \<turnstile> F" |
TTC_Imp :"(\<sim>nnf phi) \<bullet> \<Delta> \<turnstile> F \<Longrightarrow>  psi \<bullet> \<Delta> \<turnstile> F 
           \<Longrightarrow> (phi .\<longrightarrow> psi) # \<Delta> \<turnstile> F" |
TTC_Alw : "phi \<bullet> (\<circle>(\<box> phi)) \<bullet> \<Delta>  \<turnstile> F 
           \<Longrightarrow> (\<box> phi) #  \<Delta> \<turnstile> F"  |
TTC_R :  "phi \<bullet> psi \<bullet> \<Delta> \<turnstile> F \<Longrightarrow> psi \<bullet> (\<circle>(phi \<R> psi)) \<bullet> \<Delta> \<turnstile> F 
                            \<Longrightarrow> (phi \<R> psi) # \<Delta> \<turnstile> F" |
TTC_Evt : "phi \<bullet> \<Delta>  \<turnstile> F \<Longrightarrow> (\<circle>(\<diamond> phi)) \<bullet> \<Delta>  \<turnstile> F 
             \<Longrightarrow> (\<diamond> phi) # \<Delta> \<turnstile> F" |
TTC_U : " psi \<bullet> \<Delta> \<turnstile> F \<Longrightarrow> phi \<bullet> (\<circle>(phi \<U> psi)) \<bullet> \<Delta> \<turnstile> F 
            \<Longrightarrow> (phi \<U> psi) # \<Delta> \<turnstile> F" |
TTC_Evt_Plus : "phi \<bullet> \<Delta> \<turnstile> F   \<Longrightarrow>  (\<circle>((negCtxt \<Delta>) \<dieresis>\<U>\<dieresis> phi)) \<bullet> \<Delta> \<turnstile> F 
             \<Longrightarrow> (\<diamond> phi) # \<Delta> \<turnstile> F" |
TTC_U_Plus : "psi \<bullet> \<Delta> \<turnstile> F  
          \<Longrightarrow>  phi \<bullet> (\<circle>((phi .\<sqinter>. (negCtxt \<Delta>)) \<dieresis>\<U>\<dieresis> psi)) \<bullet> \<Delta> \<turnstile> F  
          \<Longrightarrow> (phi \<U> psi) # \<Delta> \<turnstile> F"  |
(* Unnext Rule *)
TTC_Next_State : "(next_state \<Delta>) \<turnstile> F \<Longrightarrow> \<Delta> \<turnstile> F" |

(* Additional rules for automation*)
TTC_Interchange : "(sort \<Delta>) \<turnstile> F \<Longrightarrow> \<Delta> \<turnstile> F" |
TTC_U_Sel : "psi \<bullet> \<Delta> \<turnstile> F  
            \<Longrightarrow>  phi \<bullet> (\<circle>((phi .\<sqinter>. (negCtxt \<Delta>)) \<dieresis>\<U>\<dieresis> psi)) \<bullet> \<Delta> \<turnstile> F   
            \<Longrightarrow> (phi \<dieresis>\<U>\<dieresis> psi) # \<Delta> \<turnstile> F" |
TTC_Mark_Next : "(\<dieresis>\<circle>\<dieresis> phi) \<bullet> \<Delta> \<turnstile> F \<Longrightarrow> (\<circle> phi) # \<Delta> \<turnstile> F" |
TTC_Unmark_Next : "(\<circle> phi)  \<bullet> \<Delta> \<turnstile> F \<Longrightarrow> (\<dieresis>\<circle>\<dieresis> phi) # \<Delta> \<turnstile> F" 

end (* Theory TTC_Calculus *)