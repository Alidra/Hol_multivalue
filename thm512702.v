Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm512702_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm11004_spec.
Require Import thm11005_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21740_spec.
Require Import thm21760_spec.
Require Import thm21772_spec.
Require Import thm21774_spec.
Lemma lem511999 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term0 _17389 P e Q) : term0 _17389 P e Q.
Proof. exact (h1). Qed.
Lemma lem512002 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term1 _17389 P e Q) : term1 _17389 P e Q.
Proof. exact (h1). Qed.
Lemma lem512003 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : term2 _17389 P e Q.
Proof. exact (fun h0 : term1 _17389 P e Q => @lem512002 _17389 P e Q h0). Qed.
Lemma lem512004 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term2 _17389 P e Q) : term2 _17389 P e Q.
Proof. exact (h1). Qed.
Lemma lem512005 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term1 _17389 P e Q) : term1 _17389 P e Q.
Proof. exact (h1). Qed.
Lemma lem512006 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term1 _17389 P e Q) (h2 : term2 _17389 P e Q) : term1 _17389 P e Q.
Proof. exact (@lem512004 _17389 P e Q h2 (@lem512005 _17389 P e Q h1)). Qed.
Lemma lem512007 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term1 _17389 P e Q) : term3 _17389 P e Q.
Proof. exact (fun h0 : term2 _17389 P e Q => @lem512006 _17389 P e Q h1 h0). Qed.
Lemma lem512008 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term2 _17389 P e Q) : term2 _17389 P e Q.
Proof. exact (h1). Qed.
Lemma lem512009 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term1 _17389 P e Q) (h2 : term2 _17389 P e Q) : term1 _17389 P e Q.
Proof. exact (@lem512007 _17389 P e Q h1 (@lem512008 _17389 P e Q h2)). Qed.
Lemma lem512010 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term2 _17389 P e Q) : term2 _17389 P e Q.
Proof. exact (fun h0 : term1 _17389 P e Q => @lem512009 _17389 P e Q h0 h1). Qed.
Lemma lem512011 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : term4 _17389 P e Q.
Proof. exact (fun h0 : term2 _17389 P e Q => @lem512010 _17389 P e Q h0). Qed.
Lemma lem512014 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : term2 _17389 P e Q.
Proof. exact (@lem512011 _17389 P e Q (@lem512003 _17389 P e Q)). Qed.
Lemma lem512015 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : term2 _17389 P e Q.
Proof. exact (@lem512014 _17389 P e Q). Qed.
Lemma lem512029 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem512030 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term1 _17389 P e Q) = (term5 _17389 P e Q).
Proof. exact (@lem512029 (term0 _17389 P e Q)). Qed.
Lemma lem512032 (t : Prop) : (term6 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem512033 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term5 _17389 P e Q) = ((term7 _17389 P e Q) = (term8 _17389 P e Q)).
Proof. exact (@lem512032 ((term7 _17389 P e Q) = (term8 _17389 P e Q))). Qed.
Lemma lem512034 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term1 _17389 P e Q) = ((term7 _17389 P e Q) = (term8 _17389 P e Q)).
Proof. exact (TRANS (@lem512030 _17389 P e Q) (@lem512033 _17389 P e Q)). Qed.
Lemma lem512045 {_17389 : Type'} (e : _17389) (Q : Prop) : (term9 _17389 e Q) = (term10 _17389 e Q).
Proof. exact (fun_ext (fun P : _17389 -> Prop => @lem512034 _17389 P e Q)). Qed.
Lemma lem512046 {_17389 : Type'} : (@all (_17389 -> Prop)) = (@all (_17389 -> Prop)).
Proof. exact (eq_refl (@all (_17389 -> Prop))). Qed.
Lemma lem512047 {_17389 : Type'} (e : _17389) (Q : Prop) : (term11 _17389 e Q) = (term12 _17389 e Q).
Proof. exact (MK_COMB (@lem512046 _17389) (@lem512045 _17389 e Q)). Qed.
Lemma lem512052 {_17389 : Type'} (Q : Prop) : (term13 _17389 Q) = (term14 _17389 Q).
Proof. exact (fun_ext (fun e : _17389 => @lem512047 _17389 e Q)). Qed.
Lemma lem512053 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512054 {_17389 : Type'} (Q : Prop) : (term15 _17389 Q) = (term16 _17389 Q).
Proof. exact (MK_COMB (@lem512053 _17389) (@lem512052 _17389 Q)). Qed.
Lemma lem512059 {_17389 : Type'} : (term17 _17389) = (term18 _17389).
Proof. exact (fun_ext (fun Q : Prop => @lem512054 _17389 Q)). Qed.
Lemma lem512060 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem512069 {_17389 : Type'} : (term19 _17389) = (term20 _17389).
Proof. exact (MK_COMB (@lem512060) (@lem512059 _17389)). Qed.
Lemma lem512074 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term8 _17389 P e Q) = (term8 _17389 P e Q).
Proof. exact (eq_refl (term8 _17389 P e Q)). Qed.
Lemma lem512083 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) (Q : Prop) : (term21 _17389 P m e Q) = (term21 _17389 P m e Q).
Proof. exact (eq_refl (term21 _17389 P m e Q)). Qed.
Lemma lem512084 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term22 _17389 P e Q) = (term22 _17389 P e Q).
Proof. exact (fun_ext (fun m : _17389 => @lem512083 _17389 P m e Q)). Qed.
Lemma lem512085 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512086 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term7 _17389 P e Q) = (term7 _17389 P e Q).
Proof. exact (MK_COMB (@lem512085 _17389) (@lem512084 _17389 P e Q)). Qed.
Lemma lem512087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem512088 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term23 _17389 P e Q) = (term23 _17389 P e Q).
Proof. exact (MK_COMB (@lem512087) (@lem512086 _17389 P e Q)). Qed.
Lemma lem512089 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : ((term7 _17389 P e Q) = (term8 _17389 P e Q)) = ((term7 _17389 P e Q) = (term8 _17389 P e Q)).
Proof. exact (MK_COMB (@lem512088 _17389 P e Q) (@lem512074 _17389 P e Q)). Qed.
Lemma lem512090 {_17389 : Type'} (e : _17389) (Q : Prop) : (term10 _17389 e Q) = (term10 _17389 e Q).
Proof. exact (fun_ext (fun P : _17389 -> Prop => @lem512089 _17389 P e Q)). Qed.
Lemma lem512091 {_17389 : Type'} : (@all (_17389 -> Prop)) = (@all (_17389 -> Prop)).
Proof. exact (eq_refl (@all (_17389 -> Prop))). Qed.
Lemma lem512092 {_17389 : Type'} (e : _17389) (Q : Prop) : (term12 _17389 e Q) = (term12 _17389 e Q).
Proof. exact (MK_COMB (@lem512091 _17389) (@lem512090 _17389 e Q)). Qed.
Lemma lem512093 {_17389 : Type'} (Q : Prop) : (term14 _17389 Q) = (term14 _17389 Q).
Proof. exact (fun_ext (fun e : _17389 => @lem512092 _17389 e Q)). Qed.
Lemma lem512094 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512095 {_17389 : Type'} (Q : Prop) : (term16 _17389 Q) = (term16 _17389 Q).
Proof. exact (MK_COMB (@lem512094 _17389) (@lem512093 _17389 Q)). Qed.
Lemma lem512096 {_17389 : Type'} : (term18 _17389) = (term18 _17389).
Proof. exact (fun_ext (fun Q : Prop => @lem512095 _17389 Q)). Qed.
Lemma lem512097 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem512098 {_17389 : Type'} : (term20 _17389) = (term20 _17389).
Proof. exact (MK_COMB (@lem512097) (@lem512096 _17389)). Qed.
Lemma lem512099 {_17389 : Type'} : (term19 _17389) = (term20 _17389).
Proof. exact (TRANS (@lem512069 _17389) (@lem512098 _17389)). Qed.
Lemma lem512105 (P : Prop -> Prop) : (term24 P) = (term25 P).
Proof. exact (EQ_MP (@lem11005 P) (@lem11004 P)). Qed.
Lemma lem512106 {_17389 : Type'} : (term26 _17389) = (term27 _17389).
Proof. exact (@lem512105 (term18 _17389)). Qed.
Lemma lem512107 {_17389 : Type'} (Q : Prop) : (term28 _17389 Q) = (term16 _17389 Q).
Proof. exact (eq_refl (term28 _17389 Q)). Qed.
Lemma lem512108 {_17389 : Type'} : (term29 _17389) = (term18 _17389).
Proof. exact (fun_ext (fun Q : Prop => @lem512107 _17389 Q)). Qed.
Lemma lem512109 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem512110 {_17389 : Type'} : (term26 _17389) = (term20 _17389).
Proof. exact (MK_COMB (@lem512109) (@lem512108 _17389)). Qed.
Lemma lem512111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem512112 {_17389 : Type'} : (term30 _17389) = (term31 _17389).
Proof. exact (MK_COMB (@lem512111) (@lem512110 _17389)). Qed.
Lemma lem512113 {_17389 : Type'} : (term32 _17389) = (term33 _17389).
Proof. exact (eq_refl (term32 _17389)). Qed.
Lemma lem512114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512115 {_17389 : Type'} : (term34 _17389) = (term35 _17389).
Proof. exact (MK_COMB (@lem512114) (@lem512113 _17389)). Qed.
Lemma lem512116 {_17389 : Type'} : (term36 _17389) = (term37 _17389).
Proof. exact (eq_refl (term36 _17389)). Qed.
Lemma lem512117 {_17389 : Type'} : (term27 _17389) = (term38 _17389).
Proof. exact (MK_COMB (@lem512115 _17389) (@lem512116 _17389)). Qed.
Lemma lem512118 {_17389 : Type'} : ((term26 _17389) = (term27 _17389)) = ((term20 _17389) = (term38 _17389)).
Proof. exact (MK_COMB (@lem512112 _17389) (@lem512117 _17389)). Qed.
Lemma lem512119 {_17389 : Type'} : (term20 _17389) = (term38 _17389).
Proof. exact (EQ_MP (@lem512118 _17389) (@lem512106 _17389)). Qed.
Lemma lem512143 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem21772 t)). Qed.
Lemma lem512144 {_17389 : Type'} (m : _17389) (e : _17389) : (term39 _17389 m e) = True.
Proof. exact (@lem512143 (m = e)). Qed.
Lemma lem512145 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) : (term40 _17389 P m) = (term40 _17389 P m).
Proof. exact (eq_refl (term40 _17389 P m)). Qed.
Lemma lem512146 {_17389 : Type'} (e : _17389) (P : _17389 -> Prop) (m : _17389) : (term41 _17389 P m e) = (term42 _17389 P m).
Proof. exact (MK_COMB (@lem512145 _17389 P m) (@lem512144 _17389 m e)). Qed.
Lemma lem512148 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem21772 t)). Qed.
Lemma lem512149 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) : (term42 _17389 P m) = True.
Proof. exact (@lem512148 (P m)). Qed.
Lemma lem512150 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term41 _17389 P m e) = True.
Proof. exact (TRANS (@lem512146 _17389 e P m) (@lem512149 _17389 P m)). Qed.
Lemma lem512151 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term43 _17389 P e) = (term44 _17389).
Proof. exact (fun_ext (fun m : _17389 => @lem512150 _17389 P m e)). Qed.
Lemma lem512152 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512153 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term45 _17389 P e) = (term46 _17389).
Proof. exact (MK_COMB (@lem512152 _17389) (@lem512151 _17389 P e)). Qed.
Lemma lem512155 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem512156 {_17389 : Type'} (t : Prop) : (term47 _17389 t) = t.
Proof. exact (@lem512155 _17389 t). Qed.
Lemma lem512157 {_17389 : Type'} : (term46 _17389) = True.
Proof. exact (@lem512156 _17389 True). Qed.
Lemma lem512158 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term45 _17389 P e) = True.
Proof. exact (TRANS (@lem512153 _17389 P e) (@lem512157 _17389)). Qed.
Lemma lem512159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem512160 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term48 _17389 P e) = (@eq Prop True).
Proof. exact (MK_COMB (@lem512159) (@lem512158 _17389 P e)). Qed.
Lemma lem512162 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem21772 t)). Qed.
Lemma lem512163 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term42 _17389 P e) = True.
Proof. exact (@lem512162 (P e)). Qed.
Lemma lem512164 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : ((term45 _17389 P e) = (term42 _17389 P e)) = (True = True).
Proof. exact (MK_COMB (@lem512160 _17389 P e) (@lem512163 _17389 P e)). Qed.
Lemma lem512166 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem21740 t)). Qed.
Lemma lem512167 : (True = True) = True.
Proof. exact (@lem512166 True). Qed.
Lemma lem512168 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : ((term45 _17389 P e) = (term42 _17389 P e)) = True.
Proof. exact (TRANS (@lem512164 _17389 P e) (@lem512167)). Qed.
Lemma lem512169 {_17389 : Type'} (e : _17389) : (term49 _17389 e) = (term50 _17389).
Proof. exact (fun_ext (fun P : _17389 -> Prop => @lem512168 _17389 P e)). Qed.
Lemma lem512170 {_17389 : Type'} : (@all (_17389 -> Prop)) = (@all (_17389 -> Prop)).
Proof. exact (eq_refl (@all (_17389 -> Prop))). Qed.
Lemma lem512171 {_17389 : Type'} (e : _17389) : (term51 _17389 e) = (term52 _17389).
Proof. exact (MK_COMB (@lem512170 _17389) (@lem512169 _17389 e)). Qed.
Lemma lem512173 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem512174 {_17389 : Type'} (t : Prop) : (term53 _17389 t) = t.
Proof. exact (@lem512173 (_17389 -> Prop) t). Qed.
Lemma lem512175 {_17389 : Type'} : (term52 _17389) = True.
Proof. exact (@lem512174 _17389 True). Qed.
Lemma lem512176 {_17389 : Type'} (e : _17389) : (term51 _17389 e) = True.
Proof. exact (TRANS (@lem512171 _17389 e) (@lem512175 _17389)). Qed.
Lemma lem512177 {_17389 : Type'} : (term54 _17389) = (term44 _17389).
Proof. exact (fun_ext (fun e : _17389 => @lem512176 _17389 e)). Qed.
Lemma lem512178 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512179 {_17389 : Type'} : (term33 _17389) = (term46 _17389).
Proof. exact (MK_COMB (@lem512178 _17389) (@lem512177 _17389)). Qed.
Lemma lem512181 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem512182 {_17389 : Type'} (t : Prop) : (term47 _17389 t) = t.
Proof. exact (@lem512181 _17389 t). Qed.
Lemma lem512183 {_17389 : Type'} : (term46 _17389) = True.
Proof. exact (@lem512182 _17389 True). Qed.
Lemma lem512184 {_17389 : Type'} : (term33 _17389) = True.
Proof. exact (TRANS (@lem512179 _17389) (@lem512183 _17389)). Qed.
Lemma lem512185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512186 {_17389 : Type'} : (term35 _17389) = (and True).
Proof. exact (MK_COMB (@lem512185) (@lem512184 _17389)). Qed.
Lemma lem512208 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem21774 t)). Qed.
Lemma lem512209 {_17389 : Type'} (m : _17389) (e : _17389) : (term55 _17389 m e) = (term56 _17389 m e).
Proof. exact (@lem512208 (m = e)). Qed.
Lemma lem512210 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) : (term40 _17389 P m) = (term40 _17389 P m).
Proof. exact (eq_refl (term40 _17389 P m)). Qed.
Lemma lem512211 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term57 _17389 P m e) = (term58 _17389 P m e).
Proof. exact (MK_COMB (@lem512210 _17389 P m) (@lem512209 _17389 m e)). Qed.
Lemma lem512214 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term59 _17389 P e) = (term60 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512211 _17389 P m e)). Qed.
Lemma lem512215 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512216 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term61 _17389 P e) = (term62 _17389 P e).
Proof. exact (MK_COMB (@lem512215 _17389) (@lem512214 _17389 P e)). Qed.
Lemma lem512223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem512224 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term63 _17389 P e) = (term64 _17389 P e).
Proof. exact (MK_COMB (@lem512223) (@lem512216 _17389 P e)). Qed.
Lemma lem512226 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem21774 t)). Qed.
Lemma lem512227 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term65 _17389 P e) = (term66 _17389 P e).
Proof. exact (@lem512226 (P e)). Qed.
Lemma lem512228 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : ((term61 _17389 P e) = (term65 _17389 P e)) = ((term62 _17389 P e) = (term66 _17389 P e)).
Proof. exact (MK_COMB (@lem512224 _17389 P e) (@lem512227 _17389 P e)). Qed.
Lemma lem512229 {_17389 : Type'} (e : _17389) : (term67 _17389 e) = (term68 _17389 e).
Proof. exact (fun_ext (fun P : _17389 -> Prop => @lem512228 _17389 P e)). Qed.
Lemma lem512230 {_17389 : Type'} : (@all (_17389 -> Prop)) = (@all (_17389 -> Prop)).
Proof. exact (eq_refl (@all (_17389 -> Prop))). Qed.
Lemma lem512231 {_17389 : Type'} (e : _17389) : (term69 _17389 e) = (term70 _17389 e).
Proof. exact (MK_COMB (@lem512230 _17389) (@lem512229 _17389 e)). Qed.
Lemma lem512238 {_17389 : Type'} : (term71 _17389) = (term72 _17389).
Proof. exact (fun_ext (fun e : _17389 => @lem512231 _17389 e)). Qed.
Lemma lem512239 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512240 {_17389 : Type'} : (term37 _17389) = (term73 _17389).
Proof. exact (MK_COMB (@lem512239 _17389) (@lem512238 _17389)). Qed.
Lemma lem512247 {_17389 : Type'} : (term38 _17389) = (term74 _17389).
Proof. exact (MK_COMB (@lem512186 _17389) (@lem512240 _17389)). Qed.
Lemma lem512249 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem21760 t)). Qed.
Lemma lem512250 {_17389 : Type'} : (term74 _17389) = (term73 _17389).
Proof. exact (@lem512249 (term73 _17389)). Qed.
Lemma lem512271 {_17389 : Type'} : (term38 _17389) = (term73 _17389).
Proof. exact (TRANS (@lem512247 _17389) (@lem512250 _17389)). Qed.
Lemma lem512272 {_17389 : Type'} : (term20 _17389) = (term73 _17389).
Proof. exact (TRANS (@lem512119 _17389) (@lem512271 _17389)). Qed.
Lemma lem512273 {_17389 : Type'} : (term19 _17389) = (term73 _17389).
Proof. exact (TRANS (@lem512099 _17389) (@lem512272 _17389)). Qed.
Lemma lem512274 {_17389 : Type'} : (term73 _17389) = (term19 _17389).
Proof. exact (SYM (@lem512273 _17389)). Qed.
Lemma lem512276 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem512277 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : ((term62 _17389 P e) = (term66 _17389 P e)) = (term76 _17389 P e).
Proof. exact (@lem512276 ((term62 _17389 P e) = (term66 _17389 P e))). Qed.
Lemma lem512278 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term76 _17389 P e) = ((term62 _17389 P e) = (term66 _17389 P e)).
Proof. exact (SYM (@lem512277 _17389 P e)). Qed.
Lemma lem512279 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term77 _17389 P e) : term77 _17389 P e.
Proof. exact (h1). Qed.
Lemma lem512285 {_17389 : Type'} (m : _17389) (e : _17389) : (term78 _17389 m e) = (m = e).
Proof. exact (@lem16933 (m = e)). Qed.
Lemma lem512287 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) : (term79 _17389 P m) = (term79 _17389 P m).
Proof. exact (eq_refl (term79 _17389 P m)). Qed.
Lemma lem512288 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term80 _17389 P m e) = (term81 _17389 P m e).
Proof. exact (MK_COMB (@lem512287 _17389 P m) (@lem512285 _17389 m e)). Qed.
Lemma lem512289 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term82 _17389 P m e) = (term80 _17389 P m e).
Proof. exact (@lem17362 (P m) (term56 _17389 m e)). Qed.
Lemma lem512290 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term82 _17389 P m e) = (term81 _17389 P m e).
Proof. exact (TRANS (@lem512289 _17389 P m e) (@lem512288 _17389 P m e)). Qed.
Lemma lem512295 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term58 _17389 P m e) = (term83 _17389 P m e).
Proof. exact (@lem17265 (P m) (term56 _17389 m e)). Qed.
Lemma lem512296 {_17389 : Type'} (P : _17389 -> Prop) : (term84 _17389 P) = (term85 _17389 P).
Proof. exact (@lem18392 _17389 P). Qed.
Lemma lem512297 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term86 _17389 P e) = (term87 _17389 P e).
Proof. exact (@lem512296 _17389 (term60 _17389 P e)). Qed.
Lemma lem512298 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term88 _17389 P e m) = (term58 _17389 P m e).
Proof. exact (eq_refl (term88 _17389 P e m)). Qed.
Lemma lem512299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem512300 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term89 _17389 P e m) = (term82 _17389 P m e).
Proof. exact (MK_COMB (@lem512299) (@lem512298 _17389 P m e)). Qed.
Lemma lem512301 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term89 _17389 P e m) = (term81 _17389 P m e).
Proof. exact (TRANS (@lem512300 _17389 P m e) (@lem512290 _17389 P m e)). Qed.
Lemma lem512302 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term90 _17389 P e) = (term91 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512301 _17389 P m e)). Qed.
Lemma lem512303 {_17389 : Type'} : (@ex _17389) = (@ex _17389).
Proof. exact (eq_refl (@ex _17389)). Qed.
Lemma lem512304 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term87 _17389 P e) = (term92 _17389 P e).
Proof. exact (MK_COMB (@lem512303 _17389) (@lem512302 _17389 P e)). Qed.
Lemma lem512305 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term86 _17389 P e) = (term92 _17389 P e).
Proof. exact (TRANS (@lem512297 _17389 P e) (@lem512304 _17389 P e)). Qed.
Lemma lem512306 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term60 _17389 P e) = (term93 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512295 _17389 P m e)). Qed.
Lemma lem512307 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512308 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term62 _17389 P e) = (term94 _17389 P e).
Proof. exact (MK_COMB (@lem512307 _17389) (@lem512306 _17389 P e)). Qed.
Lemma lem512309 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term66 _17389 P e) = (term66 _17389 P e).
Proof. exact (eq_refl (term66 _17389 P e)). Qed.
Lemma lem512312 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term95 _17389 P e) = (P e).
Proof. exact (@lem16933 (P e)). Qed.
Lemma lem512313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512314 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term96 _17389 P e) = (term97 _17389 P e).
Proof. exact (MK_COMB (@lem512313) (@lem512305 _17389 P e)). Qed.
Lemma lem512315 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term98 _17389 P e) = (term99 _17389 P e).
Proof. exact (MK_COMB (@lem512314 _17389 P e) (@lem512309 _17389 P e)). Qed.
Lemma lem512316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512317 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term100 _17389 P e) = (term101 _17389 P e).
Proof. exact (MK_COMB (@lem512316) (@lem512308 _17389 P e)). Qed.
Lemma lem512318 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term102 _17389 P e) = (term103 _17389 P e).
Proof. exact (MK_COMB (@lem512317 _17389 P e) (@lem512312 _17389 P e)). Qed.
Lemma lem512319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem512320 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term104 _17389 P e) = (term105 _17389 P e).
Proof. exact (MK_COMB (@lem512319) (@lem512318 _17389 P e)). Qed.
Lemma lem512321 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term106 _17389 P e) = (term107 _17389 P e).
Proof. exact (MK_COMB (@lem512320 _17389 P e) (@lem512315 _17389 P e)). Qed.
Lemma lem512322 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term77 _17389 P e) = (term106 _17389 P e).
Proof. exact (@lem17646 (term62 _17389 P e) (term66 _17389 P e)). Qed.
Lemma lem512323 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term77 _17389 P e) = (term107 _17389 P e).
Proof. exact (TRANS (@lem512322 _17389 P e) (@lem512321 _17389 P e)). Qed.
Lemma lem512402 {A : Type'} (P : A -> Prop) (Q : Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem512403 {_17389 : Type'} (P : _17389 -> Prop) (Q : Prop) : (term108 _17389 P Q) = (term109 _17389 P Q).
Proof. exact (@lem512402 _17389 P Q). Qed.
Lemma lem512404 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term110 _17389 P e) = (term111 _17389 P e).
Proof. exact (@lem512403 _17389 (term91 _17389 P e) (term66 _17389 P e)). Qed.
Lemma lem512405 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term112 _17389 P e m) = (term81 _17389 P m e).
Proof. exact (eq_refl (term112 _17389 P e m)). Qed.
Lemma lem512406 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term113 _17389 P e) = (term91 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512405 _17389 P m e)). Qed.
Lemma lem512407 {_17389 : Type'} : (@ex _17389) = (@ex _17389).
Proof. exact (eq_refl (@ex _17389)). Qed.
Lemma lem512408 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term114 _17389 P e) = (term92 _17389 P e).
Proof. exact (MK_COMB (@lem512407 _17389) (@lem512406 _17389 P e)). Qed.
Lemma lem512409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512410 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term115 _17389 P e) = (term97 _17389 P e).
Proof. exact (MK_COMB (@lem512409) (@lem512408 _17389 P e)). Qed.
Lemma lem512411 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term66 _17389 P e) = (term66 _17389 P e).
Proof. exact (eq_refl (term66 _17389 P e)). Qed.
Lemma lem512412 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term110 _17389 P e) = (term99 _17389 P e).
Proof. exact (MK_COMB (@lem512410 _17389 P e) (@lem512411 _17389 P e)). Qed.
Lemma lem512413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem512414 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term116 _17389 P e) = (term117 _17389 P e).
Proof. exact (MK_COMB (@lem512413) (@lem512412 _17389 P e)). Qed.
Lemma lem512415 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term112 _17389 P e m) = (term81 _17389 P m e).
Proof. exact (eq_refl (term112 _17389 P e m)). Qed.
Lemma lem512416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512417 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term118 _17389 P e m) = (term119 _17389 P m e).
Proof. exact (MK_COMB (@lem512416) (@lem512415 _17389 P m e)). Qed.
Lemma lem512418 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term66 _17389 P e) = (term66 _17389 P e).
Proof. exact (eq_refl (term66 _17389 P e)). Qed.
Lemma lem512419 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : (term120 _17389 m P e) = (term121 _17389 m P e).
Proof. exact (MK_COMB (@lem512417 _17389 P m e) (@lem512418 _17389 P e)). Qed.
Lemma lem512420 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term122 _17389 P e) = (term123 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512419 _17389 m P e)). Qed.
Lemma lem512421 {_17389 : Type'} : (@ex _17389) = (@ex _17389).
Proof. exact (eq_refl (@ex _17389)). Qed.
Lemma lem512422 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term111 _17389 P e) = (term124 _17389 P e).
Proof. exact (MK_COMB (@lem512421 _17389) (@lem512420 _17389 P e)). Qed.
Lemma lem512423 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : ((term110 _17389 P e) = (term111 _17389 P e)) = ((term99 _17389 P e) = (term124 _17389 P e)).
Proof. exact (MK_COMB (@lem512414 _17389 P e) (@lem512422 _17389 P e)). Qed.
Lemma lem512424 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term99 _17389 P e) = (term124 _17389 P e).
Proof. exact (EQ_MP (@lem512423 _17389 P e) (@lem512404 _17389 P e)). Qed.
Lemma lem512425 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term105 _17389 P e) = (term105 _17389 P e).
Proof. exact (eq_refl (term105 _17389 P e)). Qed.
Lemma lem512426 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term107 _17389 P e) = (term125 _17389 P e).
Proof. exact (MK_COMB (@lem512425 _17389 P e) (@lem512424 _17389 P e)). Qed.
Lemma lem512428 {A : Type'} (P : Prop) (Q : A -> Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem512429 {_17389 : Type'} (P : Prop) (Q : _17389 -> Prop) : (term126 _17389 P Q) = (term127 _17389 P Q).
Proof. exact (@lem512428 _17389 P Q). Qed.
Lemma lem512430 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term128 _17389 P e) = (term129 _17389 P e).
Proof. exact (@lem512429 _17389 (term103 _17389 P e) (term123 _17389 P e)). Qed.
Lemma lem512431 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : (term130 _17389 P e m) = (term121 _17389 m P e).
Proof. exact (eq_refl (term130 _17389 P e m)). Qed.
Lemma lem512432 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term131 _17389 P e) = (term123 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512431 _17389 m P e)). Qed.
Lemma lem512433 {_17389 : Type'} : (@ex _17389) = (@ex _17389).
Proof. exact (eq_refl (@ex _17389)). Qed.
Lemma lem512434 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term132 _17389 P e) = (term124 _17389 P e).
Proof. exact (MK_COMB (@lem512433 _17389) (@lem512432 _17389 P e)). Qed.
Lemma lem512435 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term105 _17389 P e) = (term105 _17389 P e).
Proof. exact (eq_refl (term105 _17389 P e)). Qed.
Lemma lem512436 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term128 _17389 P e) = (term125 _17389 P e).
Proof. exact (MK_COMB (@lem512435 _17389 P e) (@lem512434 _17389 P e)). Qed.
Lemma lem512437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem512438 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term133 _17389 P e) = (term134 _17389 P e).
Proof. exact (MK_COMB (@lem512437) (@lem512436 _17389 P e)). Qed.
Lemma lem512439 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : (term130 _17389 P e m) = (term121 _17389 m P e).
Proof. exact (eq_refl (term130 _17389 P e m)). Qed.
Lemma lem512440 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term105 _17389 P e) = (term105 _17389 P e).
Proof. exact (eq_refl (term105 _17389 P e)). Qed.
Lemma lem512441 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : (term135 _17389 P e m) = (term136 _17389 m P e).
Proof. exact (MK_COMB (@lem512440 _17389 P e) (@lem512439 _17389 m P e)). Qed.
Lemma lem512442 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term137 _17389 P e) = (term138 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512441 _17389 m P e)). Qed.
Lemma lem512443 {_17389 : Type'} : (@ex _17389) = (@ex _17389).
Proof. exact (eq_refl (@ex _17389)). Qed.
Lemma lem512444 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term129 _17389 P e) = (term139 _17389 P e).
Proof. exact (MK_COMB (@lem512443 _17389) (@lem512442 _17389 P e)). Qed.
Lemma lem512445 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : ((term128 _17389 P e) = (term129 _17389 P e)) = ((term125 _17389 P e) = (term139 _17389 P e)).
Proof. exact (MK_COMB (@lem512438 _17389 P e) (@lem512444 _17389 P e)). Qed.
Lemma lem512446 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term125 _17389 P e) = (term139 _17389 P e).
Proof. exact (EQ_MP (@lem512445 _17389 P e) (@lem512430 _17389 P e)). Qed.
Lemma lem512448 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term107 _17389 P e) = (term139 _17389 P e).
Proof. exact (TRANS (@lem512426 _17389 P e) (@lem512446 _17389 P e)). Qed.
Lemma lem512449 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term77 _17389 P e) = (term139 _17389 P e).
Proof. exact (TRANS (@lem512323 _17389 P e) (@lem512448 _17389 P e)). Qed.
Lemma lem512450 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term77 _17389 P e) : term139 _17389 P e.
Proof. exact (EQ_MP (@lem512449 _17389 P e) (@lem512279 _17389 P e h1)). Qed.
Lemma lem512451 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term136 _17389 m P e) : term136 _17389 m P e.
Proof. exact (h1). Qed.
Lemma lem512470 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : (term121 _17389 m P e) = (term121 _17389 m P e).
Proof. exact (eq_refl (term121 _17389 m P e)). Qed.
Lemma lem512473 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (P e) = (P e).
Proof. exact (eq_refl (P e)). Qed.
Lemma lem512488 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term83 _17389 P m e) = (term83 _17389 P m e).
Proof. exact (eq_refl (term83 _17389 P m e)). Qed.
Lemma lem512489 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term93 _17389 P e) = (term93 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512488 _17389 P m e)). Qed.
Lemma lem512490 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512491 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term94 _17389 P e) = (term94 _17389 P e).
Proof. exact (MK_COMB (@lem512490 _17389) (@lem512489 _17389 P e)). Qed.
Lemma lem512492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem512493 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term101 _17389 P e) = (term101 _17389 P e).
Proof. exact (MK_COMB (@lem512492) (@lem512491 _17389 P e)). Qed.
Lemma lem512494 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term103 _17389 P e) = (term103 _17389 P e).
Proof. exact (MK_COMB (@lem512493 _17389 P e) (@lem512473 _17389 P e)). Qed.
Lemma lem512495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem512496 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term105 _17389 P e) = (term105 _17389 P e).
Proof. exact (MK_COMB (@lem512495) (@lem512494 _17389 P e)). Qed.
Lemma lem512497 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : (term136 _17389 m P e) = (term136 _17389 m P e).
Proof. exact (MK_COMB (@lem512496 _17389 P e) (@lem512470 _17389 m P e)). Qed.
Lemma lem512498 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term136 _17389 m P e) : term136 _17389 m P e.
Proof. exact (EQ_MP (@lem512497 _17389 m P e) (@lem512451 _17389 m P e h1)). Qed.
Lemma lem512499 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term103 _17389 P e.
Proof. exact (h1). Qed.
Lemma lem512500 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : term121 _17389 m P e.
Proof. exact (h1). Qed.
Lemma lem512502 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term94 _17389 P e.
Proof. exact (proj1 (@lem512499 _17389 P e h1)). Qed.
Lemma lem512504 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : term81 _17389 P m e.
Proof. exact (proj1 (@lem512500 _17389 m P e h1)). Qed.
Lemma lem512514 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) (e : _17389) : (term83 _17389 P m e) = (term83 _17389 P m e).
Proof. exact (eq_refl (term83 _17389 P m e)). Qed.
Lemma lem512515 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term93 _17389 P e) = (term93 _17389 P e).
Proof. exact (fun_ext (fun m : _17389 => @lem512514 _17389 P m e)). Qed.
Lemma lem512516 {_17389 : Type'} : (@all _17389) = (@all _17389).
Proof. exact (eq_refl (@all _17389)). Qed.
Lemma lem512518 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term94 _17389 P e) = (term94 _17389 P e).
Proof. exact (MK_COMB (@lem512516 _17389) (@lem512515 _17389 P e)). Qed.
Lemma lem512519 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term94 _17389 P e.
Proof. exact (EQ_MP (@lem512518 _17389 P e) (@lem512502 _17389 P e h1)). Qed.
Lemma lem512536 {_17389 : Type'} (_10680 : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term140 _17389 P e _10680.
Proof. exact (@lem512519 _17389 P e h1 _10680). Qed.
Lemma lem512537 {_17389 : Type'} (P : _17389 -> Prop) (_10680 : _17389) (e : _17389) : (term140 _17389 P e _10680) = (term83 _17389 P _10680 e).
Proof. exact (eq_refl (term140 _17389 P e _10680)). Qed.
Lemma lem512544 {_17389 : Type'} (_10680 : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term83 _17389 P _10680 e.
Proof. exact (EQ_MP (@lem512537 _17389 P _10680 e) (@lem512536 _17389 _10680 P e h1)). Qed.
Lemma lem512550 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : P m.
Proof. exact (proj1 (@lem512504 _17389 m P e h1)). Qed.
Lemma lem512552 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : m = e.
Proof. exact (proj2 (@lem512504 _17389 m P e h1)). Qed.
Lemma lem512580 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : term66 _17389 P e.
Proof. exact (proj2 (@lem512500 _17389 m P e h1)). Qed.
Lemma lem512581 {_17389 : Type'} (P : _17389 -> Prop) : (term141 _17389 P) = (term141 _17389 P).
Proof. exact (eq_refl (term141 _17389 P)). Qed.
Lemma lem512582 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : (term142 _17389 P m) = (term142 _17389 P e).
Proof. exact (MK_COMB (@lem512581 _17389 P) (@lem512552 _17389 m P e h1)). Qed.
Lemma lem512583 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term142 _17389 P e) = (P e).
Proof. exact (eq_refl (term142 _17389 P e)). Qed.
Lemma lem512584 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) : (term143 _17389 P m) = (term143 _17389 P m).
Proof. exact (eq_refl (term143 _17389 P m)). Qed.
Lemma lem512585 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : ((term142 _17389 P m) = (term142 _17389 P e)) = ((term142 _17389 P m) = (P e)).
Proof. exact (MK_COMB (@lem512584 _17389 P m) (@lem512583 _17389 P e)). Qed.
Lemma lem512586 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) : (term142 _17389 P m) = (P m).
Proof. exact (eq_refl (term142 _17389 P m)). Qed.
Lemma lem512587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem512588 {_17389 : Type'} (P : _17389 -> Prop) (m : _17389) : (term143 _17389 P m) = (term144 _17389 P m).
Proof. exact (MK_COMB (@lem512587) (@lem512586 _17389 P m)). Qed.
Lemma lem512589 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (P e) = (P e).
Proof. exact (eq_refl (P e)). Qed.
Lemma lem512590 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : ((term142 _17389 P m) = (P e)) = ((P m) = (P e)).
Proof. exact (MK_COMB (@lem512588 _17389 P m) (@lem512589 _17389 P e)). Qed.
Lemma lem512591 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) : ((term142 _17389 P m) = (term142 _17389 P e)) = ((P m) = (P e)).
Proof. exact (TRANS (@lem512585 _17389 m P e) (@lem512590 _17389 m P e)). Qed.
Lemma lem512592 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : (P m) = (P e).
Proof. exact (EQ_MP (@lem512591 _17389 m P e) (@lem512582 _17389 m P e h1)). Qed.
Lemma lem512609 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : P e.
Proof. exact (proj2 (@lem512499 _17389 P e h1)). Qed.
Lemma lem512610 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term145 _17389 P e.
Proof. exact (fun h0 : term66 _17389 P e => @lem512609 _17389 P e h1). Qed.
Lemma lem512612 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem512613 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term145 _17389 P e) = (P e).
Proof. exact (@lem512612 (P e)). Qed.
Lemma lem512614 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : P e.
Proof. exact (EQ_MP (@lem512613 _17389 P e) (@lem512610 _17389 P e h1)). Qed.
Lemma lem512616 {_17389 : Type'} (x : _17389) : x = x.
Proof. exact (@lem21386 _17389 x). Qed.
Lemma lem512617 {_17389 : Type'} (x : _17389) : x = x.
Proof. exact (@lem512616 _17389 x). Qed.
Lemma lem512618 {_17389 : Type'} (e : _17389) : e = e.
Proof. exact (@lem512617 _17389 e). Qed.
Lemma lem512619 {_17389 : Type'} (e : _17389) : term147 _17389 e.
Proof. exact (fun h0 : term148 _17389 e => @lem512618 _17389 e). Qed.
Lemma lem512621 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem512622 {_17389 : Type'} (e : _17389) : (term147 _17389 e) = (e = e).
Proof. exact (@lem512621 (e = e)). Qed.
Lemma lem512623 {_17389 : Type'} (e : _17389) : e = e.
Proof. exact (EQ_MP (@lem512622 _17389 e) (@lem512619 _17389 e)). Qed.
Lemma lem512625 (a : Prop) (b : Prop) : (term149 a b) = (term150 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem512626 {_17389 : Type'} (P : _17389 -> Prop) (_10680 : _17389) (e : _17389) : (term83 _17389 P _10680 e) = (term151 _17389 P _10680 e).
Proof. exact (@lem512625 (P _10680) (_10680 = e)). Qed.
Lemma lem512628 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem512629 {_17389 : Type'} (P : _17389 -> Prop) (_10680 : _17389) (e : _17389) : (term151 _17389 P _10680 e) = (term152 _17389 P _10680 e).
Proof. exact (@lem512628 (term81 _17389 P _10680 e)). Qed.
Lemma lem512630 {_17389 : Type'} (P : _17389 -> Prop) (_10680 : _17389) (e : _17389) : (term83 _17389 P _10680 e) = (term152 _17389 P _10680 e).
Proof. exact (TRANS (@lem512626 _17389 P _10680 e) (@lem512629 _17389 P _10680 e)). Qed.
Lemma lem512632 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term153 _17389 P e.
Proof. exact (conj (@lem512614 _17389 P e h1) (@lem512623 _17389 e)). Qed.
Lemma lem512634 {_17389 : Type'} (_10680 : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term152 _17389 P _10680 e.
Proof. exact (EQ_MP (@lem512630 _17389 P _10680 e) (@lem512544 _17389 _10680 P e h1)). Qed.
Lemma lem512635 {_17389 : Type'} (_10680 : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term152 _17389 P _10680 e.
Proof. exact (@lem512634 _17389 _10680 P e h1). Qed.
Lemma lem512636 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term154 _17389 P e.
Proof. exact (@lem512635 _17389 e P e h1). Qed.
Lemma lem512639 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : False.
Proof. exact (@lem512636 _17389 P e h1 (@lem512632 _17389 P e h1)). Qed.
Lemma lem512640 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : term155.
Proof. exact (fun h0 : ~ False => @lem512639 _17389 P e h1). Qed.
Lemma lem512642 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem512643 : term155 = False.
Proof. exact (@lem512642 False). Qed.
Lemma lem512644 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term103 _17389 P e) : False.
Proof. exact (EQ_MP (@lem512643) (@lem512640 _17389 P e h1)). Qed.
Lemma lem512646 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : P e.
Proof. exact (EQ_MP (@lem512592 _17389 m P e h1) (@lem512550 _17389 m P e h1)). Qed.
Lemma lem512647 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : term145 _17389 P e.
Proof. exact (fun h0 : term66 _17389 P e => @lem512646 _17389 m P e h1). Qed.
Lemma lem512649 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem512650 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term145 _17389 P e) = (P e).
Proof. exact (@lem512649 (P e)). Qed.
Lemma lem512651 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : P e.
Proof. exact (EQ_MP (@lem512650 _17389 P e) (@lem512647 _17389 m P e h1)). Qed.
Lemma lem512654 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem512656 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term66 _17389 P e) = (term65 _17389 P e).
Proof. exact (@lem512654 (P e)). Qed.
Lemma lem512659 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : term65 _17389 P e.
Proof. exact (EQ_MP (@lem512656 _17389 P e) (@lem512580 _17389 m P e h1)). Qed.
Lemma lem512662 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : False.
Proof. exact (@lem512659 _17389 m P e h1 (@lem512651 _17389 m P e h1)). Qed.
Lemma lem512663 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : term155.
Proof. exact (fun h0 : ~ False => @lem512662 _17389 m P e h1). Qed.
Lemma lem512665 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem512666 : term155 = False.
Proof. exact (@lem512665 False). Qed.
Lemma lem512668 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term121 _17389 m P e) : False.
Proof. exact (EQ_MP (@lem512666) (@lem512663 _17389 m P e h1)). Qed.
Lemma lem512669 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term136 _17389 m P e) : False.
Proof. exact (or_elim (@lem512498 _17389 m P e h1) (fun h0 : term103 _17389 P e => @lem512644 _17389 P e h0) (fun h0 : term121 _17389 m P e => @lem512668 _17389 m P e h0)). Qed.
Lemma lem512670 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term136 _17389 m P e) : (term136 _17389 m P e) = False.
Proof. exact (prop_ext (fun h2 : term136 _17389 m P e => @lem512669 _17389 m P e h1) (fun h2 : False => @lem512498 _17389 m P e h1)). Qed.
Lemma lem512671 {_17389 : Type'} (m : _17389) (P : _17389 -> Prop) (e : _17389) (h1 : term136 _17389 m P e) : False.
Proof. exact (EQ_MP (@lem512670 _17389 m P e h1) (@lem512498 _17389 m P e h1)). Qed.
Lemma lem512672 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term77 _17389 P e) : False.
Proof. exact (ex_elim (@lem512450 _17389 P e h1) (fun m : _17389 => fun h0 : term138 _17389 P e m => @lem512671 _17389 m P e h0)). Qed.
Lemma lem512673 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term77 _17389 P e) : (term77 _17389 P e) = False.
Proof. exact (prop_ext (fun h2 : term77 _17389 P e => @lem512672 _17389 P e h1) (fun h2 : False => @lem512279 _17389 P e h1)). Qed.
Lemma lem512674 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (h1 : term77 _17389 P e) : False.
Proof. exact (EQ_MP (@lem512673 _17389 P e h1) (@lem512279 _17389 P e h1)). Qed.
Lemma lem512675 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : term76 _17389 P e.
Proof. exact (fun h0 : term77 _17389 P e => @lem512674 _17389 P e h0). Qed.
Lemma lem512676 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) : (term62 _17389 P e) = (term66 _17389 P e).
Proof. exact (EQ_MP (@lem512278 _17389 P e) (@lem512675 _17389 P e)). Qed.
Lemma lem512681 {_17389 : Type'} (e : _17389) : term70 _17389 e.
Proof. exact (fun P : _17389 -> Prop => @lem512676 _17389 P e). Qed.
Lemma lem512686 {_17389 : Type'} : term73 _17389.
Proof. exact (fun e : _17389 => @lem512681 _17389 e). Qed.
Lemma lem512687 {_17389 : Type'} : term19 _17389.
Proof. exact (EQ_MP (@lem512274 _17389) (@lem512686 _17389)). Qed.
Lemma lem512688 {_17389 : Type'} (Q : Prop) : term156 _17389 Q.
Proof. exact (@lem512687 _17389 Q). Qed.
Lemma lem512689 {_17389 : Type'} (Q : Prop) : (term156 _17389 Q) = (term15 _17389 Q).
Proof. exact (eq_refl (term156 _17389 Q)). Qed.
Lemma lem512690 {_17389 : Type'} (Q : Prop) : term15 _17389 Q.
Proof. exact (EQ_MP (@lem512689 _17389 Q) (@lem512688 _17389 Q)). Qed.
Lemma lem512691 {_17389 : Type'} (Q : Prop) (e : _17389) : term157 _17389 Q e.
Proof. exact (@lem512690 _17389 Q e). Qed.
Lemma lem512692 {_17389 : Type'} (e : _17389) (Q : Prop) : (term157 _17389 Q e) = (term11 _17389 e Q).
Proof. exact (eq_refl (term157 _17389 Q e)). Qed.
Lemma lem512693 {_17389 : Type'} (e : _17389) (Q : Prop) : term11 _17389 e Q.
Proof. exact (EQ_MP (@lem512692 _17389 e Q) (@lem512691 _17389 Q e)). Qed.
Lemma lem512694 {_17389 : Type'} (e : _17389) (Q : Prop) (P : _17389 -> Prop) : term158 _17389 e Q P.
Proof. exact (@lem512693 _17389 e Q P). Qed.
Lemma lem512695 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term158 _17389 e Q P) = (term1 _17389 P e Q).
Proof. exact (eq_refl (term158 _17389 e Q P)). Qed.
Lemma lem512696 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : term1 _17389 P e Q.
Proof. exact (EQ_MP (@lem512695 _17389 P e Q) (@lem512694 _17389 e Q P)). Qed.
Lemma lem512698 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : term1 _17389 P e Q.
Proof. exact (@lem512015 _17389 P e Q (@lem512696 _17389 P e Q)). Qed.
Lemma lem512699 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term0 _17389 P e Q) : False.
Proof. exact (@lem512698 _17389 P e Q (@lem511999 _17389 P e Q h1)). Qed.
Lemma lem512700 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term0 _17389 P e Q) : (term0 _17389 P e Q) = False.
Proof. exact (prop_ext (fun h2 : term0 _17389 P e Q => @lem512699 _17389 P e Q h1) (fun h2 : False => @lem511999 _17389 P e Q h1)). Qed.
Lemma lem512701 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) (h1 : term0 _17389 P e Q) : False.
Proof. exact (EQ_MP (@lem512700 _17389 P e Q h1) (@lem511999 _17389 P e Q h1)). Qed.
Lemma lem512702 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : term1 _17389 P e Q.
Proof. exact (fun h0 : term0 _17389 P e Q => @lem512701 _17389 P e Q h0). Qed.
