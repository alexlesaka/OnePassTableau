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

(* We will prove (one-by-one) the soundness of each inference rule in the TTC_Calculus ****)

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

(*
In order to prove the soundness of the rule TTC_U_Plus, 
we firstly prove the soundness of a similar rule that we call TTC_U_Plus_Pure
(which is really the (\<U>)^+ rule introduced in the paper
"Dual Systems of Tableaux and Sequents for PLTL" ), 
TTC_U_Plus_Pure uses the negation of the full context i.e. it also adds the 
negation of the always-formulas in the context, 
whereas in the TTC_U_Plus these formulas are filtered out.
Also, TTC_U_Plus uses subsumption in the negation of the context.
After proving the soundness of TTC_U_Plus_Pure, we will extend the result to both 
improvements: the filtering of always-formulas and the subsumption.
*)

(************ TTC_U_Plus_Pure_Sound **************)

(******* Auxiliary lemmas ************)

lemma disjNeg_l2r_Lemma:
  assumes "\<sigma> \<Turnstile> disjNeg \<Phi>"
  shows "\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>"
proof -
  from assms show ?thesis  by (induct \<Phi> rule: disjNeg.induct) (auto simp add: models_def)
qed

lemma disjNeg_r2l_Lemma:
  assumes "\<phi> .\<in> \<Phi>"
  assumes "\<sigma> \<Turnstile> \<sim>nnf \<phi>"
  shows "\<sigma> \<Turnstile> disjNeg \<Phi>"
proof -
  from assms have "\<not>(\<sigma> \<Turnstile> \<phi>)" by simp
  then have "\<not>(\<sigma> \<TTurnstile> \<Phi>)" using assms models_def by blast
  then show ?thesis by (induct \<Phi> rule: disjNeg.induct)  (auto simp add: models_def)
qed

lemma disjNeg_Lemma:
  shows "(\<sigma> \<Turnstile> disjNeg \<Phi>) \<longleftrightarrow> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<sigma> \<Turnstile> \<sim>nnf \<phi>)"
  using disjNeg_l2r_Lemma disjNeg_r2l_Lemma by blast

lemma all_context_Lemma:
  assumes "\<not>(\<sigma> \<TTurnstile> \<Delta>)" 
  shows "\<sigma> \<Turnstile> (disjNeg \<Delta>)"
  using assms models_def disjNeg_Lemma equiv_NNF  by auto

(************* soundness of TTC_U_Plus_Pure *****************)

lemma TTC_U_Plus_Pure_Sound:
  assumes "sat((\<phi> \<U> \<psi>) # \<Delta>)"
  shows "sat(\<psi> \<bullet>  \<Delta>) \<or>
         sat(\<phi> \<bullet> (\<circle>((\<phi> .\<and> disjNeg(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>)"
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
               then have Pcontext: "\<forall>j.( (h < j \<and> j < k) \<longrightarrow> (suffix \<sigma> j \<Turnstile> (disjNeg \<Delta>)))" 
                         using all_context_Lemma by auto
               then have Pphicontext: "\<forall>j. ((h < j \<and> j < k) \<longrightarrow> (suffix \<sigma> j) \<Turnstile> (\<phi> .\<and> disjNeg(\<Delta>)))"
                         using Pi Pk Pcontext 
                         by (metis Suc_lessI holds.simps(5) less_trans not_less_eq)
               then have Puntil: "(suffix \<sigma> k) \<Turnstile> \<psi> \<and> 
                                  (\<forall>j.( (h < j \<and> j < k) \<longrightarrow> (suffix \<sigma> j) \<Turnstile> (\<phi> .\<and> disjNeg(\<Delta>))))"
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
                                    (\<forall>j<i. ((suffix \<sigma>'' j)  \<Turnstile> (\<phi> .\<and> disjNeg(\<Delta>))))))"
                            using calculation Puntil by auto
                then have  "\<sigma>'' = (suffix \<sigma>' 1)" by (simp add: \<sigma>''_def \<sigma>'_def)
                then have  "\<sigma>' \<Turnstile> (\<circle>((\<phi> .\<and> disjNeg(\<Delta>)) \<U> \<psi>))"
                           using Psigma'' holds.simps(11) holds.simps(9) by blast
                then have  "\<sigma>' \<Turnstile> \<phi> \<and> \<sigma>' \<Turnstile> (\<circle>((\<phi> .\<and> disjNeg(\<Delta>)) \<U> \<psi>)) \<and>
                                   \<sigma>' \<TTurnstile> \<Delta>" 
                            by (metis Pi Pk Pkh Suc_lessI \<open>h < k\<close> \<sigma>'_def less_trans not_less_eq)
               then have "\<sigma>' \<TTurnstile> \<phi> \<bullet> (\<circle>((\<phi> .\<and> disjNeg(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>" by simp
               then show ?thesis  using sat_def by blast
             qed
             then show ?thesis by simp
           qed
           then show ?thesis by simp
         qed

(********************   TTC_U_Plus_Sound    **********************)

(*********** Auxiliary lemmas for the filtering out of always-formulas *************)

lemma forever_Lemma:
  assumes "\<sigma> \<TTurnstile> \<Phi>"
  shows "\<forall>\<alpha>.((\<box>\<alpha>) .\<in> \<Phi> \<longrightarrow> (\<forall>k.((suffix \<sigma> k) \<Turnstile> (\<box>\<alpha>))))"
  using assms models_def by auto

lemma member_of_list_Lemma :
  shows "(\<phi> .\<in> \<Delta>) = (\<phi> \<in> set \<Delta>)"
  by (induct \<Delta>) auto

lemma filterAlw_l2r_Lemma:
  shows "\<phi> .\<in> (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Phi>) \<longrightarrow> (\<phi> .\<in> \<Phi> \<and> (\<forall>\<alpha>.(\<not>(\<phi> = \<box>\<alpha>))))"
proof(induct \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons a \<Phi>)   
  have "\<phi> .\<in> (filter (\<lambda>phi.(\<not>(isAlw phi))) (Cons a \<Phi>)) \<longrightarrow>
                       \<phi> .\<in>  \<Phi> \<or> (\<phi> = a \<or>  (\<lambda>phi.(\<not>(isAlw phi))) \<phi>)" 
               by (metis Cons.hyps filter.simps(2) inlist.simps(2))
    then show ?case using Cons.hyps by auto
  qed 

lemma filterAlw_r2l_Lemma:
  assumes "\<phi> .\<in> \<Phi>"
  assumes "\<forall>\<alpha>.(\<not>(\<phi> = \<box>\<alpha>))"
  shows "\<phi> .\<in> (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Phi>)"
proof -
  have Pfilter: "(\<phi> \<in> set (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Phi>)) 
                  \<longleftrightarrow> (\<phi> \<in> (set \<Phi>)  \<and> ((\<lambda>phi.(\<not>(isAlw phi))) \<phi>))" by simp
  from assms have "((\<lambda>phi.(\<not>(isAlw phi))) \<phi>) = True" using isAlw.elims(2) by auto
  then show ?thesis using member_of_list_Lemma  assms(1) by auto
qed

lemma filterAlw_Lemma:
  shows "\<phi> .\<in> (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Phi>) \<longleftrightarrow> (\<phi> .\<in> \<Phi> \<and> (\<forall>\<alpha>.(\<not>(\<phi> = \<box>\<alpha>))))"
  using filterAlw_l2r_Lemma filterAlw_r2l_Lemma by blast

lemma negCtxt_Lemma:
  assumes "\<sigma> \<TTurnstile> \<Phi>"
  assumes "i \<ge> 1"
  assumes "(suffix \<sigma> i) \<Turnstile> (disjNeg \<Phi>)"
  shows "(suffix \<sigma> i) \<Turnstile> (negCtxt \<Phi>)"
proof -
  from assms(3) have "(\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> (suffix \<sigma> i) \<Turnstile> \<sim>nnf \<phi>)" 
                     using disjNeg_Lemma by simp
  then have "\<not>(\<Phi> = []) \<and> (\<exists>\<phi>. \<phi> .\<in> \<Phi> \<and> \<not>((suffix \<sigma> i) \<Turnstile> \<phi>))" by auto
  then have P: "\<not>(\<Phi> = []) \<and> (\<exists>\<phi>.(\<phi> .\<in> \<Phi> \<and> \<not>((suffix \<sigma> i) \<Turnstile> \<phi>) \<and> (\<forall>\<alpha>.(\<not>(\<phi> =(\<box>\<alpha>))))))"
             using assms(1) forever_Lemma by blast
  then have "\<not>(\<Phi> = []) \<and> (\<exists>\<phi>.(\<phi> .\<in> (filter (\<lambda>phi.(\<not>(isAlw phi))) \<Phi>) \<and> \<not>((suffix \<sigma> i) \<Turnstile> \<phi>)))"
    using filterAlw_Lemma by blast
  then show ?thesis by (metis disjNeg_Lemma equiv_NNF negCtxt.elims) 
qed

lemma reduced_Ctxt_Lemma: 
  assumes "\<sigma> \<TTurnstile> \<Phi>" 
  assumes "\<sigma> \<Turnstile> \<circle>((\<phi> .\<and> (disjNeg \<Phi>)) \<U> \<psi>)"
  shows "\<sigma> \<Turnstile> \<circle>((\<phi> .\<and> (negCtxt \<Phi>)) \<U> \<psi>)"
proof(cases)
  assume "\<sigma> \<Turnstile> \<circle>\<psi>"
  then show ?thesis by auto
next
  assume "\<not>(\<sigma> \<Turnstile> \<circle>\<psi>)"
  define \<sigma>' where "\<sigma>' = (suffix \<sigma> 1)"
  from assms have P: "\<exists>k.(k\<ge> 1 \<and> (suffix \<sigma>' k) \<Turnstile>  \<psi> 
                       \<and> (\<forall>j<k.((suffix \<sigma>' j) \<Turnstile> (\<phi> .\<and> (disjNeg \<Phi>)))))" 
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

(*********** auxiliary lemmas for the  .\<sqinter>. ***************)

lemma disj2set_Lemma:
  shows "\<sigma> \<Turnstile> \<phi> \<longleftrightarrow> (\<exists>\<gamma>. \<gamma> \<in> (disj2set \<phi>) \<and> \<sigma> \<Turnstile> \<gamma>)" 
  by (induct \<phi>) auto
 
lemma conj2setOfsets_Lemma:
  shows "\<sigma> \<Turnstile> \<phi> \<longleftrightarrow> (\<forall>\<Lambda>. \<Lambda> \<in> (conj2setOfsets \<phi>) \<longrightarrow> (\<exists>\<delta>. \<delta> \<in> \<Lambda> \<and> \<sigma> \<Turnstile> \<delta>))"
proof (induct \<phi>)
  case F
  then have "conj2setOfsets F =  (Set.insert (disj2set F) Set.empty)" by simp
  then show ?case by (metis disj2set.simps(2) insertI1 singletonD)
next
  case T
  then show ?case
    by (metis conj2setOfsets.simps(3) disj2set.simps(3) singletonD singletonI)
next
  case (Var x)
  then show ?case
    by (metis conj2setOfsets.simps(4) disj2set.simps(4) insertI1 singletonD)
next
  case (Not \<phi>)
  then show ?case
    by (metis conj2setOfsets.simps(5) disj2set.simps(5) insertI1 singletonD)
next
  case (And \<phi>1 \<phi>2)
  then show ?case
    by (metis (full_types) Un_iff conj2setOfsets.simps(1) holds.simps(5))
next
  case (Or \<phi>1 \<phi>2)
  then show ?case
    by (metis conj2setOfsets.simps(6) disj2set_Lemma insertI1 singletonD)
next
  case (Imp \<phi>1 \<phi>2)
  then show ?case
    by (metis conj2setOfsets.simps(7) disj2set.simps(7) singletonD singletonI)
next
  case (X \<phi>)
  then show ?case
    by (metis conj2setOfsets.simps(8) disj2set.simps(8) insertI1 singletonD)
next
  case (U \<phi>1 \<phi>2)
  then show ?case
    by (metis conj2setOfsets.simps(9) disj2set.simps(9) insertI1 singletonD)
next
  case (R \<phi>1 \<phi>2)
  then show ?case using conj2setOfsets.simps(10) singletonD
    by (metis disj2set.simps(10) singletonI)
next
  case (Alw \<phi>)
  then show ?case using conj2setOfsets.simps(11)
    by (metis disj2set.simps(11) singletonD singletonI)
next
  case (Evt \<phi>)
  then show ?case using conj2setOfsets.simps(12)
    by (metis disj2set.simps(12) insertI1 singletonD)
next
  case (SelX \<phi>)
  then show ?case using conj2setOfsets.simps(13)
    by (metis disj2set.simps(13) singletonD singletonI)
next
  case (SelU \<phi>1 \<phi>2)
  then show ?case  using conj2setOfsets.simps(14)
    by (metis disj2set.simps(14) insertI1 singletonD)
qed


lemma inclusion_Lemma:
  assumes  "\<sigma> \<Turnstile> \<phi>"
  assumes  "\<Lambda> \<in> (conj2setOfsets \<phi>)"
  assumes "\<Lambda> \<le> (disj2set \<psi>)" 
  shows  "\<sigma> \<Turnstile> \<psi>"
proof -
  show ?thesis using assms conj2setOfsets_Lemma disj2set_Lemma by blast
qed

lemma subsumption_Lemma:
  assumes "(Bex (conj2setOfsets \<phi>) (\<lambda>S. S \<le> (disj2set \<psi>)))"
  assumes "\<sigma> \<Turnstile> \<phi>"
  shows  "\<sigma> \<Turnstile> \<phi> .\<and> \<psi>"
proof -
  from assms(1) have "\<exists>\<Lambda>.((\<Lambda> \<in> (conj2setOfsets \<phi>)) \<and>  (\<Lambda> \<le> (disj2set \<psi>)))" by auto
  then show ?thesis using inclusion_Lemma using assms(2) holds.simps(5) by blast
qed

lemma conjWSmp_Lemma:
  shows "\<sigma> \<Turnstile> \<phi> .\<and> \<psi> = \<sigma> \<Turnstile> \<phi> .\<sqinter>. \<psi>"
proof(cases "(Bex (conj2setOfsets \<phi>) (\<lambda>S. S \<le> (disj2set \<psi>)))")
  case True
  have "\<sigma> \<Turnstile> \<phi> .\<and> \<psi> \<longrightarrow> \<sigma> \<Turnstile> \<phi>" by auto
  then have "\<sigma> \<Turnstile> \<phi> .\<and> \<psi> = \<sigma> \<Turnstile> \<phi>" using subsumption_Lemma using True by blast
  then show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed

(************* Soundness of TTC_U_Plus *************)

lemma TTC_U_Plus_Sound:
  assumes "unSat(\<psi> \<bullet>  \<Delta>)"
  assumes "unSat(\<phi> \<bullet> (\<circle>((\<phi> .\<sqinter>. negCtxt(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>)"  
  shows "unSat((\<phi> \<U> \<psi>) # \<Delta>)"
proof -
  have "sat(\<phi> \<bullet> (\<circle>((\<phi> .\<sqinter>. negCtxt(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>)  = sat(\<phi> \<bullet> (\<circle>((\<phi> .\<and> negCtxt(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>)"
    using conjWSmp_Lemma models_list sat_def by auto
  thus ?thesis 
  using reduced_Ctxt_Lemma TTC_U_Plus_Pure_Sound assms models_list sat_def unSat_def
  by (metis (no_types, lifting))
qed

(************* TTC_Next_State_Sound *************)

lemma TTC_Next_State_Sound:
  assumes "unSat(next_state \<Delta>)"
  shows "unSat(\<Delta>)"
proof (rule ccontr)
  assume "\<not>unSat(\<Delta>)"  
  then have "\<exists>\<sigma>.(\<sigma> \<TTurnstile> \<Delta>)" by (simp add: sat_def unSat_def)
  then obtain \<sigma> where  "\<sigma> \<TTurnstile> \<Delta>" by auto
  define \<sigma>' where "\<sigma>'= suffix  \<sigma> 1"
  then have "\<forall>\<phi>.((\<circle>\<phi>).\<in> \<Delta> \<or> (\<dieresis>\<circle>\<dieresis>\<phi>).\<in> \<Delta>) \<longrightarrow> (\<sigma>' \<Turnstile> \<phi>)" using \<open>\<sigma> \<TTurnstile> \<Delta>\<close> models_def by auto
  then have  "\<forall>\<phi>.(\<phi> .\<in>  map removeX (filter isX \<Delta>)) \<longrightarrow> (\<sigma>' \<Turnstile> \<phi>)" 
    by (smt filter_set imageE isX.elims(2) member_filter member_of_list_Lemma 
            removeX.simps(1) removeX.simps(2) set_map) 
  then have "\<sigma>' \<TTurnstile> (next_state \<Delta>)"  by (simp add: models_def)
  then show "False" using assms sat_def unSat_def by blast
qed


(*****  Soundness of the additional rules for automation *********)

(******************  TTC_Interchange_Sound ***********************)

lemma  TTC_Interchange_Sound:
  shows "sat(sort \<Delta>) = sat(\<Delta>)"
proof - 
  have Psort: "\<forall>\<sigma>.(\<sigma> \<TTurnstile> sort \<Delta> = \<sigma> \<TTurnstile> \<Delta>)"
proof (induct \<Delta>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Delta>)
  have  "\<sigma> \<TTurnstile> (insert \<psi> \<Delta>) = (\<sigma> \<Turnstile> \<psi> \<and> \<sigma> \<TTurnstile> \<Delta>)" by simp  
  then show ?case using  models_def Cons.hyps by auto
qed
have "sat(sort \<Delta>) = sat (\<Delta>)" using Psort unSat_def sat_def models_def by simp
then show ?thesis by auto
qed

(************************  TTC_U_Sel_Sound ***********************)

lemma TTC_U_Sel_Sound:
  assumes "unSat(\<psi> \<bullet>  \<Delta>)"
  assumes "unSat(\<phi> \<bullet> (\<circle>((\<phi> .\<sqinter>. negCtxt(\<Delta>)) \<U> \<psi>)) \<bullet> \<Delta>)"  
  shows "unSat((\<phi> \<dieresis>\<U>\<dieresis> \<psi>) # \<Delta>)"
proof -
  have "\<forall>\<sigma>.(\<sigma> \<Turnstile> \<phi> \<dieresis>\<U>\<dieresis> \<psi> = \<sigma> \<Turnstile> \<phi> \<U> \<psi>)" by auto
  then have  "unSat((\<phi> \<dieresis>\<U>\<dieresis> \<psi>) # \<Delta>) =  unSat((\<phi> \<U> \<psi>) # \<Delta>)" 
       using unSat_def sat_def models_def by (metis inlist.simps(2) )
     thus ?thesis using unSat_def TTC_U_Plus_Sound assms by blast
   qed

(**********  TTC_U_Mark_Next and TTC_UnMark_Next are both sound ************)

lemma TTC_Mark_Next_and_TTC_Unmark_Next_Sound:
  shows "sat((\<dieresis>\<circle>\<dieresis> phi) \<bullet> \<Delta>) = sat((\<circle> phi) \<bullet> \<Delta>)"
by (simp add: sat_def)