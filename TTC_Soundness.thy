theory TTC_Soundness
  imports TTC_Calculus 

begin

type_synonym Structure = "nat \<Rightarrow> string set" 
(* \<omega>-sequence of states of strings, each repr. all the true atoms *)

definition suffix :: "Structure \<Rightarrow> nat \<Rightarrow> Structure"
  where "suffix \<sigma> n = (\<lambda>i.(\<sigma> (n+i)))"

lemma suffix0 [simp]: "suffix \<sigma> 0 = \<sigma>"
  by (simp add: suffix_def)

lemma suffix_add [simp]: "suffix (suffix \<sigma> m) n = suffix \<sigma> (m+n)" 
  by (simp add: suffix_def add_ac)

primrec holds :: "Structure \<Rightarrow> PLTL_formula \<Rightarrow> bool"  ("(_ \<Turnstile> _)" [60,60] 59)
  where
  "\<sigma> \<Turnstile> F = False" |
  "\<sigma> \<Turnstile> T = True" |
  "\<sigma> \<Turnstile> V s = (s \<in> (\<sigma> 0))" |  
  "\<sigma> \<Turnstile> .\<not> \<phi>  = (\<not>(\<sigma> \<Turnstile> \<phi>))" |
  "\<sigma> \<Turnstile> \<phi> .\<and> \<psi> = (\<sigma> \<Turnstile> \<phi> \<and>  \<sigma> \<Turnstile> \<psi>)" |
  "\<sigma> \<Turnstile> \<phi> .\<or> \<psi> = (\<sigma> \<Turnstile> \<phi> \<or>  \<sigma> \<Turnstile> \<psi>)" |
  "\<sigma> \<Turnstile> \<phi> .\<longrightarrow> \<psi> = (\<sigma> \<Turnstile> \<phi> \<longrightarrow>  \<sigma> \<Turnstile> \<psi>)" |
  "\<sigma> \<Turnstile> \<box> \<phi>  = (\<forall>i. suffix \<sigma> i  \<Turnstile> \<phi>)" |
  "\<sigma> \<Turnstile> \<circle> \<phi>  = (suffix \<sigma> 1  \<Turnstile> \<phi>)" |
  "\<sigma> \<Turnstile> \<dieresis>\<circle>\<dieresis> \<phi>  = (suffix \<sigma> 1  \<Turnstile> \<phi>)" |
  "\<sigma> \<Turnstile> \<phi> \<U> \<psi> = (\<exists>i. suffix \<sigma> i  \<Turnstile> \<psi> \<and> (\<forall>j<i. suffix \<sigma> j  \<Turnstile> \<phi>))" |
  "\<sigma> \<Turnstile> \<diamond> \<phi>  = (\<exists>i. suffix \<sigma> i  \<Turnstile> \<phi>)" |
  "\<sigma> \<Turnstile> \<phi> \<R> \<psi> = (\<not>(\<exists>i.(\<not>(suffix \<sigma> i  \<Turnstile> \<psi>) \<and> (\<forall>j<i. \<not>(suffix \<sigma> j  \<Turnstile> \<phi>)))))" |
  "\<sigma> \<Turnstile> \<phi> \<dieresis>\<U>\<dieresis> \<psi> = (\<exists>i. suffix \<sigma> i  \<Turnstile> \<psi> \<and> (\<forall>j<i. suffix \<sigma> j  \<Turnstile> \<phi>))"

definition models :: "Structure \<Rightarrow> PLTL_formula list \<Rightarrow> bool" ("(_ \<TTurnstile> _)" [60,60] 59)
  where "models \<sigma> \<Phi> = (\<forall>\<phi>. (\<phi> .\<in> \<Phi> \<longrightarrow> \<sigma> \<Turnstile> \<phi>))"

definition sat :: "PLTL_formula list \<Rightarrow> bool" 
  where "sat \<Delta> = (\<exists>\<sigma>. \<sigma> \<TTurnstile> \<Delta>)" 

definition unSat :: "PLTL_formula list \<Rightarrow> bool" 
  where "unSat \<Delta> = (\<not>(sat \<Delta>))" 

  (******************** Some auxiliar lemmas **************)

    lemma equiv_NNF [simp]:
      shows "(\<not>(\<sigma> \<Turnstile> \<phi>)) = (\<sigma> \<Turnstile> \<sim>nnf \<phi>)"
      by (induct \<phi> arbitrary: \<sigma>) auto

    lemma equiv_order [simp]:
      shows "\<phi> .\<in> (\<psi>  \<bullet>  \<Delta>) = \<phi> .\<in> (\<psi> # \<Delta>)"
      by (induct \<Delta>) auto

    lemma unfold_not_unSat [simp]:
      shows "(\<not>(unSat \<Delta>)) =  (\<exists>\<sigma>. \<forall>\<delta>. \<delta>.\<in> \<Delta> \<longrightarrow> \<sigma> \<Turnstile> \<delta>)"
    proof - 
      show ?thesis using models_def sat_def unSat_def by blast 
    qed

    lemma models_list [simp]:
      shows "\<sigma> \<TTurnstile> (\<psi>  \<bullet>  \<Delta>) = (\<sigma> \<Turnstile> \<psi> \<and> \<sigma> \<TTurnstile> \<Delta>)"
      using models_def by auto
 
(******************** TTC_Ctd1 soundness ***************)

lemma TTC_Ctd1_Sound:
  assumes "\<phi> .\<in> \<Delta>" 
  assumes "\<sim>nnf \<phi> .\<in> \<Delta>" 
  shows "unSat \<Delta>"
proof (rule ccontr)
  assume "\<not>(unSat \<Delta>)" 
  hence "\<exists>\<sigma>. \<sigma> \<TTurnstile> \<Delta> "  by (simp add: models_def)
  then have "\<exists> \<sigma>. \<sigma> \<Turnstile>\<sim>nnf \<phi>  \<and> \<sigma> \<Turnstile> \<phi>" using models_def assms by auto
  then show "False" using equiv_NNF by blast
qed


(******************** TTC_Ctd2 soundness ***************)

lemma TTC_Ctd2_Sound:
  assumes "F .\<in> \<Delta>" 
  shows "unSat \<Delta>"
proof -
  from assms have "\<forall>\<sigma>. F.\<in> \<Delta> \<and> \<not>(\<sigma> \<Turnstile> F)" by auto
  thus ?thesis using unfold_not_unSat by blast 
qed


(******************** TTC_T soundness *****************)

lemma TTC_T_Sound [simp]:
  assumes "unSat \<Delta>"
  shows "unSat (T # \<Delta>)" 
proof -
  from assms have "\<not>(sat(T # \<Delta>))" by (simp add: models_def unSat_def sat_def)    
  then show ?thesis by (simp add: unSat_def)  
qed


(******************** TTC_And soundness ****************)

lemma TTC_And_Sound:
  assumes "unSat(\<phi> \<bullet> \<psi> \<bullet> \<Delta>)"
  shows "unSat((\<phi> .\<and> \<psi>) # \<Delta>)"
proof (rule ccontr)
  assume "\<not>(unSat((\<phi> .\<and> \<psi>) # \<Delta>))"
  then have "\<not>(unSat(\<phi> \<bullet> \<psi> \<bullet> \<Delta>))" by auto
  with assms show False by simp  
qed


(******************** TTC_Or soundness ****************)

lemma TTC_Or_Sound:
  assumes "unSat(\<phi> \<bullet> \<Delta>)"
  assumes "unSat(\<psi> \<bullet> \<Delta>)" 
  shows "unSat((\<phi> .\<or> \<psi>) # \<Delta>)" 
proof (rule ccontr)
  assume "\<not>(unSat((\<phi> .\<or> \<psi>) # \<Delta>))"
  hence "\<exists>\<sigma>.((\<sigma> \<TTurnstile> \<phi> \<bullet> \<Delta>) \<or> (\<sigma> \<TTurnstile> \<psi> \<bullet> \<Delta>))" using models_def 
         by (metis holds.simps(6) inlist.simps(2) models_list sat_def unSat_def)
  with assms show False using models_def sat_def unSat_def by blast
qed

(******************** TTC_Imp soundness ****************)

lemma TTC_Imp_Sound:
  assumes "unSat((\<sim>nnf \<phi>) \<bullet> \<Delta>)"
  assumes "unSat((\<psi> \<bullet> \<Delta>))"
  shows "unSat((\<phi> .\<longrightarrow> \<psi>) # \<Delta>)"
proof (rule ccontr)      
  assume "\<not>(unSat(\<phi> .\<longrightarrow> \<psi> # \<Delta>))"
  hence "\<exists>\<sigma>. (\<not>(\<sigma> \<Turnstile> \<phi>) \<or> \<sigma> \<Turnstile> \<psi>) \<and> (\<sigma> \<TTurnstile> \<Delta>)" 
         by (meson holds.simps(7) inlist.simps(2) models_def sat_def unSat_def)
  then have "\<exists>\<sigma>. \<sigma> \<TTurnstile> ((\<sim>nnf \<phi>) \<bullet> \<Delta>) \<or>  \<sigma> \<TTurnstile> (\<psi> \<bullet> \<Delta>)" by auto
  with assms show False using models_def sat_def unSat_def by blast
qed

(******************** TTC_Alw soundness ****************)

lemma TTC_Alw_Sound:
  assumes "unSat(\<phi> \<bullet> (\<circle>(\<box> \<phi>)) \<bullet> \<Delta>)"
  shows "unSat((\<box> \<phi>) #  \<Delta>)"
proof (rule ccontr)
  assume "\<not>(unSat((\<box> \<phi>) #  \<Delta>))"
  then have "\<exists>\<sigma>.((\<forall>i. suffix \<sigma> i  \<Turnstile> \<phi>) \<and>  \<sigma> \<TTurnstile> \<Delta>)"  
             using  models_def sat_def unSat_def 
             by (meson holds.simps(8) inlist.simps(2))
  hence "\<exists>\<sigma>.(suffix \<sigma> 0 \<Turnstile> \<phi> \<and> (\<forall>i. suffix \<sigma> (i+1) \<Turnstile> \<phi>) \<and>  \<sigma> \<TTurnstile> \<Delta>)" by blast
  then have "\<not>(unSat(\<phi> \<bullet> (\<circle>(\<box> \<phi>)) \<bullet> \<Delta>))" by (simp add: sat_def unSat_def)
  with assms show False by simp
qed


(******************** TTC_U soundness ****************)

lemma TTC_U_Sound [simp]:
  assumes "unSat(\<psi> \<bullet> \<Delta>)"
  assumes "unSat(\<phi> \<bullet> (\<circle>(\<phi> \<U> \<psi>)) \<bullet> \<Delta>)"
  shows "unSat((\<phi> \<U> \<psi>) # \<Delta>)"
proof (rule ccontr)
  assume "\<not>(unSat((\<phi> \<U> \<psi>) # \<Delta>))"
  then obtain \<sigma> where "\<sigma> \<TTurnstile>((\<phi> \<U> \<psi>) # \<Delta>)" using sat_def unSat_def by blast 
  then obtain i:: nat where hyp:
        "suffix \<sigma> i  \<Turnstile> \<psi> \<and> (\<forall>j<i. suffix \<sigma> j  \<Turnstile> \<phi>) \<and> \<sigma> \<TTurnstile> \<Delta>" using models_def by auto
  then have "sat(\<psi> \<bullet> \<Delta>) \<or> sat(\<phi> \<bullet> (\<circle>(\<phi> \<U> \<psi>)) \<bullet> \<Delta>)"
  proof (cases)
    assume  "i = 0" 
    then show ?thesis using hyp by (auto simp add: models_def sat_def)
  next
    assume "\<not>(i = 0)"
    then have "i > 0 \<and> \<sigma> \<Turnstile> \<phi> \<and> 
              suffix (suffix \<sigma> (i-1)) 1 \<Turnstile> \<psi> \<and> 
              (\<forall>j<i. suffix \<sigma> j  \<Turnstile> \<phi>) \<and>
               \<sigma> \<TTurnstile> \<Delta>" using hyp by auto 
    then have  "\<sigma> \<Turnstile> \<phi> \<and> \<sigma> \<Turnstile>  \<circle>(\<phi> \<U> \<psi>) \<and> \<sigma> \<TTurnstile> \<Delta>" by auto
    thus ?thesis  by (auto simp add: models_def sat_def)
  qed
  with assms show False using sat_def unSat_def by blast
qed

(*************** TTC_Evt soundness by equivalence \<diamond>\<phi> \<equiv> T\<U>\<phi> ***********)

lemma TTC_Evt_Sound_by_equiv:
  assumes "unSat(\<phi> \<bullet> \<Delta>)"
  assumes "unSat((\<circle> (\<diamond> \<phi>)) \<bullet> \<Delta>)"
  shows "unSat((\<diamond> \<phi>) # \<Delta>)"
proof -
  have E1: "unSat((\<circle>(\<diamond> \<phi>)) \<bullet> \<Delta>) = unSat(T \<bullet> (\<circle>(T \<U> \<phi>)) \<bullet> \<Delta>)"
       by (auto simp add: models_def unSat_def sat_def)
  have E2: "unSat((\<diamond> \<phi>) # \<Delta>) = unSat((T \<U> \<phi>) # \<Delta>)"
       by (auto simp add: models_def unSat_def sat_def)
  from assms show ?thesis using E1 E2 TTC_U_Sound[where  \<phi> = T]  by simp 
  qed

(******************** TTC_R soundness ****************)

lemma TTC_R_Sound:
  assumes "unSat(\<phi> \<bullet> \<psi> \<bullet>  \<Delta>)"
  assumes "unSat(\<psi> \<bullet> (\<circle>(\<phi> \<R> \<psi>)) \<bullet> \<Delta>)"
  shows "unSat((\<phi> \<R> \<psi>) # \<Delta>)"
proof (rule ccontr)
  assume "\<not>unSat((\<phi> \<R> \<psi>) # \<Delta>)"
  then obtain \<sigma> where P1: "(\<not>(\<exists>i. \<not>(suffix \<sigma> i  \<Turnstile> \<psi>) \<and> 
                            (\<forall>j<i. \<not>(suffix \<sigma> j  \<Turnstile> \<phi>)))) \<and> 
                             \<sigma> \<TTurnstile> \<Delta>"   
                           using models_def sat_def unSat_def
                           by (metis holds.simps(13) inlist.simps(2))
  then have "sat(\<phi> \<bullet> \<psi> \<bullet>  \<Delta>) \<or> sat(\<psi> \<bullet> (\<circle>(\<phi> \<R> \<psi>)) \<bullet> \<Delta>)"
  proof (cases)
    assume "suffix \<sigma> 0  \<Turnstile> \<psi> \<and> suffix \<sigma> 0  \<Turnstile> \<phi>"
    then show ?thesis using P1 by (auto simp add: models_def sat_def unSat_def)
  next
    assume "\<not>(suffix \<sigma> 0  \<Turnstile> \<psi> \<and> suffix \<sigma> 0  \<Turnstile> \<phi>)"
    then have P2: "\<not>(suffix \<sigma> 0  \<Turnstile> \<phi>) \<and> suffix  \<sigma> 0  \<Turnstile> \<psi>" using P1 by blast
    then have "sat(\<psi> \<bullet> (\<circle>(\<phi> \<R> \<psi>)) \<bullet> \<Delta>)"
      proof (cases)
        assume "\<forall>i. suffix \<sigma> i  \<Turnstile> \<psi>"
        then have "\<forall>i. suffix \<sigma> i \<Turnstile> \<psi> \<and> suffix \<sigma> i \<Turnstile> \<circle>(\<phi> \<R> \<psi>)" by auto 
        then have "suffix \<sigma> 0 \<Turnstile> \<psi> \<and> suffix \<sigma> 0 \<Turnstile> \<circle>(\<phi> \<R> \<psi>)" by blast 
        then show ?thesis using P1 by (auto simp add: models_def sat_def unSat_def)
      next
        assume "\<not>(\<forall>i. suffix \<sigma> i  \<Turnstile> \<psi>)"
        then obtain n::nat where "n =  (LEAST k. (\<not>(suffix  \<sigma> k \<Turnstile> \<psi>)))" by blast
        then have "(\<not>(suffix  \<sigma> n \<Turnstile> \<psi>)) \<and>                        
                    (\<forall>j<n. (suffix \<sigma> j \<Turnstile>  \<psi>))"
          by (smt LeastI \<open>\<not> (\<forall>i. suffix \<sigma> i \<Turnstile> \<psi>)\<close> P1 not_less_Least)
        then have "(\<exists>j<n. (j>0 \<and> (suffix \<sigma> j  \<Turnstile> \<phi>) \<and>
                   (\<forall>k<n. (suffix \<sigma> k  \<Turnstile>  \<psi>) )))"  using P1 P2 by (metis gr0I)
        then have "suffix \<sigma> 1 \<Turnstile> \<phi> \<R> \<psi>"
             by (smt One_nat_def Suc_leI add.commute add.left_neutral add_Suc_right 
                     add_mono_thms_linordered_semiring(1) gr0_conv_Suc holds.simps(13) 
                     le_imp_less_Suc less_imp_add_positive not_less suffix_add)
        then have "\<sigma> \<Turnstile> \<psi> \<and> \<sigma> \<Turnstile>  \<circle>(\<phi> \<R> \<psi>)" using P2 by auto 
        then show ?thesis using P1 by (auto simp add: models_def sat_def unSat_def)
      qed
      then show ?thesis by auto
  qed    
  with assms show False using sat_def unSat_def by blast
qed


(************ TTC_U_Plus_"Pure"_Sound **************)

fun neg_all_context :: "PLTL_formula list \<Rightarrow> PLTL_formula"  where
"neg_all_context [] = F" |
"neg_all_context \<Delta> = disjNeg \<Delta>"

(*
fun disjNeg :: "PLTL_formula list \<Rightarrow> PLTL_formula"  where
"disjNeg [] = F" |
"disjNeg [h] = (\<sim>nnf h)" |
"disjNeg (h#t) =  (disjNeg t) .\<or> (\<sim>nnf h)"
*)


lemma disjNeg_l2r_Lemma:
  assumes "\<sigma> \<Turnstile> disjNeg \<Phi>"
  shows " (\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>))"
proof -
  then show ?thesis sorry
qed


(*
lemma disjNeg_Lemma:
  shows "\<sigma> \<Turnstile> disjNeg \<Phi> \<longleftrightarrow> (\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>))"
proof
  have l2r: "\<sigma> \<Turnstile> disjNeg \<Phi> \<Longrightarrow> (\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>))" 
  proof 
    show "\<sigma> \<Turnstile> disjNeg \<Phi> \<Longrightarrow> \<Phi> \<noteq> []" by auto
    show "\<sigma> \<Turnstile> disjNeg \<Phi> \<Longrightarrow> \<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>" sorry
  qed
  have r2l: "(\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>)) \<Longrightarrow> \<sigma> \<Turnstile> disjNeg \<Phi>" sorry
 
(*  then show ?thesis using l2r r2l by blast *)
  oops
*)

(*
lemma neg_all_context_Lemma:
  shows "(\<sigma> \<Turnstile> neg_all_context \<Phi>) = (\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>))"
proof -
  then show ?thesis using disjNeg_Lemma 
                     by (metis (full_types) holds.simps(1) inlist.elims(2) inlist.elims(3) 
                                neg_all_context.simps(1) neg_all_context.simps(2))
qed
*)

(*
fun negCtxt :: "PLTL_formula list \<Rightarrow> PLTL_formula"  where
"negCtxt [] = F" |
"negCtxt \<Delta> = disjNeg (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Delta>)"
*)

(*
lemma forever_Lemma:
  assumes "\<sigma> \<TTurnstile> \<Phi>"
  shows "\<forall>\<alpha>.((\<box>\<alpha>) .\<in> \<Phi> \<longrightarrow> (\<forall>k.((suffix \<sigma> k) \<Turnstile> (\<box>\<alpha>))))"
proof -
  then show ?thesis sorry
qed

lemma filterAlw_Lemma:
  shows "\<phi> .\<in> (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Phi>) = (\<phi> .\<in> \<Phi> \<and> (\<forall>\<alpha>.(\<not>(\<phi> =(\<box>\<alpha>)))))"
proof -
  show ?thesis sorry
qed

lemma negCtxt_Lemma:
  assumes "\<sigma> \<TTurnstile> \<Phi>"
  assumes "i \<ge> 1"
  assumes "(suffix \<sigma> i) \<Turnstile> (neg_all_context \<Phi>)"
  shows "(suffix \<sigma> i) \<Turnstile> (negCtxt \<Phi>)"
proof -
  from assms(3) have "(\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> (suffix \<sigma> i) \<Turnstile> \<sim>nnf \<phi>))" 
                     using neg_all_context_Lemma by simp
  then have "\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<not>((suffix \<sigma> i) \<Turnstile> \<phi>))" by auto
  then have P: "\<not>(\<Phi> = []) \<and> (\<exists>\<phi>.(\<phi> .\<in> \<Phi> \<and> \<not>((suffix \<sigma> i) \<Turnstile> \<phi>) \<and> (\<forall>\<alpha>.(\<not>(\<phi> =(\<box>\<alpha>))))))"
             using assms(1) forever_Lemma by blast
  then have "\<not>(\<Phi> = []) \<and> (\<exists>\<phi>.(\<phi> .\<in> (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Phi>) \<and> \<not>((suffix \<sigma> i) \<Turnstile> \<phi>)))"
    using filterAlw_Lemma by blast
  then show ?thesis by (metis disjNeg_Lemma equiv_NNF inlist.simps(1) negCtxt.elims) 
qed

lemma reduced_Ctxt_Lemma: 
  assumes "\<sigma> \<TTurnstile> \<Phi>" 
  assumes "\<sigma> \<Turnstile> \<circle>((\<phi> .\<and> (neg_all_context \<Phi>)) \<U> \<psi>)"
  shows "\<sigma> \<Turnstile> \<circle>((\<phi> .\<and> (negCtxt \<Phi>)) \<U> \<psi>)"
proof(cases)
  assume "\<sigma> \<Turnstile> \<circle>\<psi>"
  then show ?thesis by auto
next
  assume "\<not>(\<sigma> \<Turnstile> \<circle>\<psi>)"
  define \<sigma>' where "\<sigma>' = (suffix \<sigma> 1)"
  from assms have P: "\<exists>k.(k\<ge> 1 \<and> (suffix \<sigma>' k) \<Turnstile>  \<psi> 
                       \<and> (\<forall>j<k.((suffix \<sigma>' j) \<Turnstile> (\<phi> .\<and> (neg_all_context \<Phi>)))))" 
                  using  \<open>\<not>(\<sigma> \<Turnstile> \<circle>\<psi>)\<close> \<sigma>'_def
                  by (metis (no_types, lifting) One_nat_def holds.simps(11) holds.simps(9) 
                            le_simps(3) neq0_conv suffix0)
  then obtain k where  Q: "k\<ge> 1 \<and> (suffix \<sigma>' k) \<Turnstile>  \<psi> 
                       \<and> (\<forall>j<k.((suffix \<sigma>' j) \<Turnstile> (\<phi> .\<and> (negCtxt \<Phi>))))"
                        using assms(1) \<sigma>'_def P negCtxt_Lemma 
                        by (metis One_nat_def Suc_leI holds.simps(5) plus_nat.simps(2) 
                                  suffix_add zero_less_Suc)
  then have R: "\<sigma>' \<Turnstile> (\<phi> .\<and> (negCtxt \<Phi>)) \<U> \<psi>" using Q holds.simps(11) by blast
  then show  "\<sigma> \<Turnstile> \<circle>((\<phi> .\<and> (negCtxt \<Phi>)) \<U> \<psi>)" using \<sigma>'_def by auto
qed
*)


(* 
lemma all_context_Lemma:
  assumes "\<not>(\<sigma> \<TTurnstile> \<Delta>)" 
  shows "\<sigma> \<Turnstile> (neg_all_context \<Delta>)"
  using assms models_def disjNeg_lemma equiv_NNF  
  by (metis inlist.simps(1) neg_all_context.elims) 

lemma TTC_U_Plus_Pure_Sound:
  assumes "sat((\<phi> \<U> \<psi>) # \<Delta>)"
  shows "sat(\<psi> \<bullet>  \<Delta>) \<or>
         sat(\<phi> \<bullet> (\<circle>((\<phi> .\<and> neg_all_context(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>)"
proof -
  from assms have "\<exists>\<sigma>.( \<exists>i.(suffix \<sigma> i  \<Turnstile> \<psi> \<and> (\<forall>j<i. suffix \<sigma> j  \<Turnstile> \<phi>))
                        \<and> \<sigma> \<TTurnstile> \<Delta> )"
                   by (simp add: models_def sat_def) blast
      then obtain \<sigma> and i::nat where Pi: "(\<sigma> \<TTurnstile> \<Delta>) \<and>  suffix \<sigma> i  \<Turnstile> \<psi> \<and> 
                                          (\<forall>j<i. suffix \<sigma> j  \<Turnstile> \<phi>)" by auto
      then have ?thesis
      proof(cases)
        assume "i = 0"
        then show ?thesis using Pi by (auto simp add: models_def sat_def)
      next
        assume "\<not>(i = 0)" 
        then obtain  k::"nat" where "k = (LEAST z::nat. (suffix \<sigma> z  \<Turnstile> \<psi>))" by blast
        then have Pk: "(suffix \<sigma> k  \<Turnstile> \<psi>) \<and> (\<forall>j<k. \<not>(suffix \<sigma> j  \<Turnstile> \<psi>))"
          by (meson LeastI not_less_Least Pi)
        also have "k \<ge>0" by blast
        then obtain h::"nat" where Ph: "h = (GREATEST z.(z \<le> k \<and> ((suffix \<sigma> z \<TTurnstile> \<Delta>))))" 
                     by blast
             then have Pkh: "0 \<le> k \<and> h \<le> k \<and> (suffix \<sigma> h \<TTurnstile> \<Delta>)" 
                        using Pi Pk Ph by (smt GreatestI_nat \<open>0 \<le> k\<close> le0 suffix0 zero_le)
             then have PhGreatest: "\<forall>j. ((j \<le> k \<and> suffix \<sigma> j \<TTurnstile> \<Delta>) \<longrightarrow> \<not>(h < j))"
                        by (metis (no_types, lifting) Greatest_le_nat Ph not_le)
             then have ?thesis
             proof(cases) 
               assume "h = k"
               then have "(suffix \<sigma> k \<Turnstile> \<psi>) \<and> (suffix \<sigma> k \<TTurnstile> \<Delta>)" 
                          using Pkh calculation models_def by blast
               then show ?thesis using Pk Ph models_def sat_def by auto 
             next
               assume "\<not>(h = k)"
               then have "h < k" using Pkh by auto
               then have "\<forall>j. ( (h < j \<and> j < k) \<longrightarrow> (\<not>(suffix \<sigma> j \<TTurnstile> \<Delta>)))" using  PhGreatest by auto
               then have Pcontext: "\<forall>j.( (h < j \<and> j < k) \<longrightarrow> (suffix \<sigma> j \<Turnstile> (neg_all_context \<Delta>)))" 
                         using all_context_Lemma by auto
               then have Pphicontext: "\<forall>j. ((h < j \<and> j < k) \<longrightarrow> (suffix \<sigma> j) \<Turnstile> (\<phi> .\<and> neg_all_context(\<Delta>)))"
                                      using Pi Pk Pcontext by (metis Suc_lessI holds.simps(5) less_trans not_less_eq)
               then have Puntil: "(suffix \<sigma> k) \<Turnstile> \<psi> \<and> 
                                  (\<forall>j.( (h < j \<and> j < k) \<longrightarrow> (suffix \<sigma> j) \<Turnstile> (\<phi> .\<and> neg_all_context(\<Delta>))))"
                                   using Pphicontext calculation by blast       
               define \<sigma>':: "Structure" where "\<sigma>' = (suffix \<sigma> h)"
               define \<sigma>'':: "Structure" where "\<sigma>'' = (suffix \<sigma> (h+1))"
               then have "suffix \<sigma>'' (k-(h+1)) = (suffix \<sigma> k)"   using \<open>h < k\<close> by fastforce
               also have  "\<forall>j<(k-(h+1)).(\<exists>i.(h < i \<and> i < k \<and> (suffix \<sigma>'' j) = (suffix \<sigma> i)))"
                          using \<sigma>''_def 
                          by (metis  One_nat_def Suc_pred add.commute add_Suc_right  
                                     diff_add_inverse2  gr0_conv_Suc less_diff_conv 
                                     plus_nat.simps(2) suffix_add  zero_less_diff)
                then have Psigma'': "(\<exists>i.(i = k-(h+1) \<and> suffix \<sigma>'' i  \<Turnstile> \<psi> \<and> 
                                    (\<forall>j<i. ((suffix \<sigma>'' j)  \<Turnstile> (\<phi> .\<and> neg_all_context(\<Delta>))))))"
                            using calculation Puntil by auto
                then have  "\<sigma>'' = (suffix \<sigma>' 1)" by (simp add: \<sigma>''_def \<sigma>'_def)
                then have  "\<sigma>' \<Turnstile> (\<circle>((\<phi> .\<and> neg_all_context(\<Delta>)) \<U> \<psi>))"
                           using Psigma'' holds.simps(11) holds.simps(9) by blast
                then have  "\<sigma>' \<Turnstile> \<phi> \<and> \<sigma>' \<Turnstile> (\<circle>((\<phi> .\<and> neg_all_context(\<Delta>)) \<U> \<psi>)) \<and>
                                   \<sigma>' \<TTurnstile> \<Delta>" 
                            by (metis Pi Pk Pkh Suc_lessI \<open>h < k\<close> \<sigma>'_def less_trans not_less_eq)
               then have "\<sigma>' \<TTurnstile> \<phi> \<bullet> (\<circle>((\<phi> .\<and> neg_all_context(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>" by simp
               then show ?thesis  using sat_def by blast
             qed
             then show ?thesis by simp
           qed
           then show ?thesis by simp
         qed
*)
