Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_MAP_term_abbrevs.
Require Import ALL_MAP_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1110672_spec.
Require Import thm1110673_spec.
Require Import thm1110681_spec.
Require Import thm1110682_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1231072 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1231073 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1231072 A P). Qed.
Lemma lem1231074 {A B : Type'} (R : type1402 B) (f : A -> B) : term1 A B R f.
Proof. exact (@lem1231073 A (term2 A B R f)). Qed.
Lemma lem1231075 {A B : Type'} (R : type1402 B) (f : A -> B) : (term3 A B R f) = ((term4 A B R f) = (term5 A B R f)).
Proof. exact (eq_refl (term3 A B R f)). Qed.
Lemma lem1231076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231077 {A B : Type'} (R : type1402 B) (f : A -> B) : (term6 A B R f) = (term7 A B R f).
Proof. exact (MK_COMB (@lem1231076) (@lem1231075 A B R f)). Qed.
Lemma lem1231078 {A B : Type'} (R : type1402 B) (f : A -> B) (t : list A) : (term8 A B R f t) = ((term9 A B R f t) = (term10 A B R f t)).
Proof. exact (eq_refl (term8 A B R f t)). Qed.
Lemma lem1231079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231080 {A B : Type'} (R : type1402 B) (f : A -> B) (t : list A) : (term11 A B R f t) = (term12 A B R f t).
Proof. exact (MK_COMB (@lem1231079) (@lem1231078 A B R f t)). Qed.
Lemma lem1231081 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) (t : list A) : (term13 A B R f h t) = ((term14 A B R f h t) = (term15 A B R f h t)).
Proof. exact (eq_refl (term13 A B R f h t)). Qed.
Lemma lem1231082 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) (t : list A) : (term16 A B R f h t) = (term17 A B R f h t).
Proof. exact (MK_COMB (@lem1231080 A B R f t) (@lem1231081 A B R f h t)). Qed.
Lemma lem1231083 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) : (term18 A B R f h) = (term19 A B R f h).
Proof. exact (fun_ext (fun t : list A => @lem1231082 A B R f h t)). Qed.
Lemma lem1231084 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1231085 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) : (term20 A B R f h) = (term21 A B R f h).
Proof. exact (MK_COMB (@lem1231084 A) (@lem1231083 A B R f h)). Qed.
Lemma lem1231086 {A B : Type'} (R : type1402 B) (f : A -> B) : (term22 A B R f) = (term23 A B R f).
Proof. exact (fun_ext (fun h : A => @lem1231085 A B R f h)). Qed.
Lemma lem1231087 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231088 {A B : Type'} (R : type1402 B) (f : A -> B) : (term24 A B R f) = (term25 A B R f).
Proof. exact (MK_COMB (@lem1231087 A) (@lem1231086 A B R f)). Qed.
Lemma lem1231089 {A B : Type'} (R : type1402 B) (f : A -> B) : (term26 A B R f) = (term27 A B R f).
Proof. exact (MK_COMB (@lem1231077 A B R f) (@lem1231088 A B R f)). Qed.
Lemma lem1231090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231091 {A B : Type'} (R : type1402 B) (f : A -> B) : (term28 A B R f) = (term29 A B R f).
Proof. exact (MK_COMB (@lem1231090) (@lem1231089 A B R f)). Qed.
Lemma lem1231092 {A B : Type'} (R : type1402 B) (f : A -> B) (l : list A) : (term8 A B R f l) = ((term9 A B R f l) = (term10 A B R f l)).
Proof. exact (eq_refl (term8 A B R f l)). Qed.
Lemma lem1231093 {A B : Type'} (R : type1402 B) (f : A -> B) : (term30 A B R f) = (term2 A B R f).
Proof. exact (fun_ext (fun l : list A => @lem1231092 A B R f l)). Qed.
Lemma lem1231094 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1231095 {A B : Type'} (R : type1402 B) (f : A -> B) : (term31 A B R f) = (term32 A B R f).
Proof. exact (MK_COMB (@lem1231094 A) (@lem1231093 A B R f)). Qed.
Lemma lem1231096 {A B : Type'} (R : type1402 B) (f : A -> B) : (term1 A B R f) = (term33 A B R f).
Proof. exact (MK_COMB (@lem1231091 A B R f) (@lem1231095 A B R f)). Qed.
Lemma lem1231097 {A B : Type'} (R : type1402 B) (f : A -> B) : term33 A B R f.
Proof. exact (EQ_MP (@lem1231096 A B R f) (@lem1231074 A B R f)). Qed.
Lemma lem1231124 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1231125 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1231124 A B f). Qed.
Lemma lem1231126 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1231133 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1231126 A B f) (@lem1231125 A B f)). Qed.
Lemma lem1231134 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1231133 A B f). Qed.
Lemma lem1231135 {B : Type'} (R : type1402 B) : (@List.ForallOrdPairs B R) = (@List.ForallOrdPairs B R).
Proof. exact (eq_refl (@List.ForallOrdPairs B R)). Qed.
Lemma lem1231136 {A B : Type'} (f : A -> B) (R : type1402 B) : (term4 A B R f) = (@List.ForallOrdPairs B R (@nil B)).
Proof. exact (MK_COMB (@lem1231135 B R) (@lem1231134 A B f)). Qed.
Lemma lem1231138 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (EQ_MP (@lem1110673 A r) (@lem1110672 A r)). Qed.
Lemma lem1231139 {B : Type'} (r : type1402 B) : (@List.ForallOrdPairs B r (@nil B)) = True.
Proof. exact (@lem1231138 B r). Qed.
Lemma lem1231140 {B : Type'} (R : type1402 B) : (@List.ForallOrdPairs B R (@nil B)) = True.
Proof. exact (@lem1231139 B R). Qed.
Lemma lem1231141 {A B : Type'} (R : type1402 B) (f : A -> B) : (term4 A B R f) = True.
Proof. exact (TRANS (@lem1231136 A B f R) (@lem1231140 B R)). Qed.
Lemma lem1231142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1231143 {A B : Type'} (R : type1402 B) (f : A -> B) : (term36 A B R f) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1231142) (@lem1231141 A B R f)). Qed.
Lemma lem1231145 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (EQ_MP (@lem1110673 A r) (@lem1110672 A r)). Qed.
Lemma lem1231146 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (@lem1231145 A r). Qed.
Lemma lem1231147 {A B : Type'} (R : type1402 B) (f : A -> B) : (term5 A B R f) = True.
Proof. exact (@lem1231146 A (term37 A B R f)). Qed.
Lemma lem1231148 {A B : Type'} (R : type1402 B) (f : A -> B) : ((term4 A B R f) = (term5 A B R f)) = (True = True).
Proof. exact (MK_COMB (@lem1231143 A B R f) (@lem1231147 A B R f)). Qed.
Lemma lem1231150 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1231151 : (True = True) = True.
Proof. exact (@lem1231150 True). Qed.
Lemma lem1231152 {A B : Type'} (R : type1402 B) (f : A -> B) : ((term4 A B R f) = (term5 A B R f)) = True.
Proof. exact (TRANS (@lem1231148 A B R f) (@lem1231151)). Qed.
Lemma lem1231153 {A B : Type'} (R : type1402 B) (f : A -> B) : True = ((term4 A B R f) = (term5 A B R f)).
Proof. exact (SYM (@lem1231152 A B R f)). Qed.
Lemma lem1231154 {A B : Type'} (R : type1402 B) (f : A -> B) : (term4 A B R f) = (term5 A B R f).
Proof. exact (EQ_MP (@lem1231153 A B R f) (@lem0)). Qed.
Lemma lem1231155 {A B C : Type'} (f : B -> C) : term38 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem1231156 {A B C : Type'} (f : B -> C) : (term38 A B C f) = (term39 A B C f).
Proof. exact (eq_refl (term38 A B C f)). Qed.
Lemma lem1231157 {A B C : Type'} (f : B -> C) : term39 A B C f.
Proof. exact (EQ_MP (@lem1231156 A B C f) (@lem1231155 A B C f)). Qed.
Lemma lem1231158 {A B C : Type'} (f : B -> C) (g : A -> B) : term40 A B C f g.
Proof. exact (@lem1231157 A B C f g). Qed.
Lemma lem1231159 {A B C : Type'} (f : B -> C) (g : A -> B) : (term40 A B C f g) = ((@o A B C f g) = (term41 A B C f g)).
Proof. exact (eq_refl (term40 A B C f g)). Qed.
Lemma lem1231161 {_26411 _26412 : Type'} (P : _26412 -> Prop) : term42 _26411 _26412 P.
Proof. exact (@lem1123794 _26411 _26412 P). Qed.
Lemma lem1231162 {_26411 _26412 : Type'} (P : _26412 -> Prop) : (term42 _26411 _26412 P) = (term43 _26411 _26412 P).
Proof. exact (eq_refl (term42 _26411 _26412 P)). Qed.
Lemma lem1231163 {_26411 _26412 : Type'} (P : _26412 -> Prop) : term43 _26411 _26412 P.
Proof. exact (EQ_MP (@lem1231162 _26411 _26412 P) (@lem1231161 _26411 _26412 P)). Qed.
Lemma lem1231164 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : term44 _26411 _26412 P f.
Proof. exact (@lem1231163 _26411 _26412 P f). Qed.
Lemma lem1231165 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : (term44 _26411 _26412 P f) = (term45 _26411 _26412 P f).
Proof. exact (eq_refl (term44 _26411 _26412 P f)). Qed.
Lemma lem1231166 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) : term45 _26411 _26412 P f.
Proof. exact (EQ_MP (@lem1231165 _26411 _26412 P f) (@lem1231164 _26411 _26412 P f)). Qed.
Lemma lem1231167 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (l : list _26411) : term46 _26411 _26412 P f l.
Proof. exact (@lem1231166 _26411 _26412 P f l). Qed.
Lemma lem1231168 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (l : list _26411) : (term46 _26411 _26412 P f l) = ((term47 _26411 _26412 P f l) = (term48 _26411 _26412 P f l)).
Proof. exact (eq_refl (term46 _26411 _26412 P f l)). Qed.
Lemma lem1231170 {A B : Type'} : term49 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1231171 {A B : Type'} (f : A -> B) : term50 A B f.
Proof. exact (@lem1231170 A B f). Qed.
Lemma lem1231172 {A B : Type'} (f : A -> B) : (term50 A B f) = (term51 A B f).
Proof. exact (eq_refl (term50 A B f)). Qed.
Lemma lem1231173 {A B : Type'} (f : A -> B) : term51 A B f.
Proof. exact (EQ_MP (@lem1231172 A B f) (@lem1231171 A B f)). Qed.
Lemma lem1231174 {A B : Type'} (f : A -> B) (h : A) : term52 A B f h.
Proof. exact (@lem1231173 A B f h). Qed.
Lemma lem1231175 {A B : Type'} (h : A) (f : A -> B) : (term52 A B f h) = (term53 A B h f).
Proof. exact (eq_refl (term52 A B f h)). Qed.
Lemma lem1231176 {A B : Type'} (h : A) (f : A -> B) : term53 A B h f.
Proof. exact (EQ_MP (@lem1231175 A B h f) (@lem1231174 A B f h)). Qed.
Lemma lem1231177 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term54 A B h f t.
Proof. exact (@lem1231176 A B h f t). Qed.
Lemma lem1231178 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term54 A B h f t) = ((term55 A B f h t) = (term56 A B h f t)).
Proof. exact (eq_refl (term54 A B h f t)). Qed.
Lemma lem1231189 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term55 A B f h t) = (term56 A B h f t).
Proof. exact (EQ_MP (@lem1231178 A B h f t) (@lem1231177 A B h f t)). Qed.
Lemma lem1231190 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term55 A B f h t) = (term56 A B h f t).
Proof. exact (@lem1231189 A B h f t). Qed.
Lemma lem1231191 {B : Type'} (R : type1402 B) : (@List.ForallOrdPairs B R) = (@List.ForallOrdPairs B R).
Proof. exact (eq_refl (@List.ForallOrdPairs B R)). Qed.
Lemma lem1231192 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) (t : list A) : (term14 A B R f h t) = (term57 A B R h f t).
Proof. exact (MK_COMB (@lem1231191 B R) (@lem1231190 A B h f t)). Qed.
Lemma lem1231194 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term58 A r h t) = (term59 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1231195 {B : Type'} (h : B) (r : type1402 B) (t : list B) : (term58 B r h t) = (term59 B h r t).
Proof. exact (@lem1231194 B h r t). Qed.
Lemma lem1231196 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term57 A B R h f t) = (term60 A B h R f t).
Proof. exact (@lem1231195 B (f h) R (@List.map A B f t)). Qed.
Lemma lem1231200 {_26411 _26412 : Type'} (P : _26412 -> Prop) (f : _26411 -> _26412) (l : list _26411) : (term47 _26411 _26412 P f l) = (term48 _26411 _26412 P f l).
Proof. exact (EQ_MP (@lem1231168 _26411 _26412 P f l) (@lem1231167 _26411 _26412 P f l)). Qed.
Lemma lem1231201 {A B : Type'} (P : B -> Prop) (f : A -> B) (l : list A) : (term47 A B P f l) = (term48 A B P f l).
Proof. exact (@lem1231200 A B P f l). Qed.
Lemma lem1231202 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) (t : list A) : (term61 A B R h f t) = (term62 A B R h f t).
Proof. exact (@lem1231201 A B (term63 A B R f h) f t). Qed.
Lemma lem1231204 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term41 A B C f g).
Proof. exact (EQ_MP (@lem1231159 A B C f g) (@lem1231158 A B C f g)). Qed.
Lemma lem1231205 {A B : Type'} (f : B -> Prop) (g : A -> B) : (@o A B Prop f g) = (term64 A B f g).
Proof. exact (@lem1231204 A B Prop f g). Qed.
Lemma lem1231206 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) : (term65 A B R h f) = (term66 A B R h f).
Proof. exact (@lem1231205 A B (term63 A B R f h) f). Qed.
Lemma lem1231207 {A : Type'} : (@List.Forall A) = (@List.Forall A).
Proof. exact (eq_refl (@List.Forall A)). Qed.
Lemma lem1231208 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) : (term67 A B R h f) = (term68 A B R h f).
Proof. exact (MK_COMB (@lem1231207 A) (@lem1231206 A B R h f)). Qed.
Lemma lem1231209 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1231210 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) (t : list A) : (term62 A B R h f t) = (term69 A B R h f t).
Proof. exact (MK_COMB (@lem1231208 A B R h f) (@lem1231209 A t)). Qed.
Lemma lem1231211 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) (t : list A) : (term61 A B R h f t) = (term69 A B R h f t).
Proof. exact (TRANS (@lem1231202 A B R h f t) (@lem1231210 A B R h f t)). Qed.
Lemma lem1231212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231213 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) (t : list A) : (term70 A B R h f t) = (term71 A B R h f t).
Proof. exact (MK_COMB (@lem1231212) (@lem1231211 A B R h f t)). Qed.
Lemma lem1231215 {A B : Type'} (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : (term9 A B R f t) = (term10 A B R f t).
Proof. exact (h1). Qed.
Lemma lem1231216 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : (term60 A B h R f t) = (term72 A B h R f t).
Proof. exact (MK_COMB (@lem1231213 A B R h f t) (@lem1231215 A B R f t h1)). Qed.
Lemma lem1231219 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : (term57 A B R h f t) = (term72 A B h R f t).
Proof. exact (TRANS (@lem1231196 A B h R f t) (@lem1231216 A B h R f t h1)). Qed.
Lemma lem1231220 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : (term14 A B R f h t) = (term72 A B h R f t).
Proof. exact (TRANS (@lem1231192 A B R h f t) (@lem1231219 A B h R f t h1)). Qed.
Lemma lem1231221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1231222 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : (term73 A B R f h t) = (term74 A B h R f t).
Proof. exact (MK_COMB (@lem1231221) (@lem1231220 A B h R f t h1)). Qed.
Lemma lem1231224 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term58 A r h t) = (term59 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1231225 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term58 A r h t) = (term59 A h r t).
Proof. exact (@lem1231224 A h r t). Qed.
Lemma lem1231226 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term15 A B R f h t) = (term75 A B h R f t).
Proof. exact (@lem1231225 A h (term37 A B R f) t). Qed.
Lemma lem1231230 {A B : Type'} (f : A -> B) (y : A) : (term76 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1231231 {A : Type'} (f : type1402 A) (y : A) : (term77 A f y) = (f y).
Proof. exact (@lem1231230 A (A -> Prop) f y). Qed.
Lemma lem1231232 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) : (term78 A B R f h) = (term79 A B R f h).
Proof. exact (@lem1231231 A (term37 A B R f) h). Qed.
Lemma lem1231233 {A B : Type'} (R : type1402 B) (x : A) (f : A -> B) : (term79 A B R f x) = (term66 A B R x f).
Proof. exact (eq_refl (term79 A B R f x)). Qed.
Lemma lem1231234 {A B : Type'} (R : type1402 B) (f : A -> B) : (term80 A B R f) = (term37 A B R f).
Proof. exact (fun_ext (fun x : A => @lem1231233 A B R x f)). Qed.
Lemma lem1231235 {A : Type'} (h : A) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1231236 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) : (term78 A B R f h) = (term79 A B R f h).
Proof. exact (MK_COMB (@lem1231234 A B R f) (@lem1231235 A h)). Qed.
Lemma lem1231237 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1231238 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) : (term81 A B R f h) = (term82 A B R f h).
Proof. exact (MK_COMB (@lem1231237 A) (@lem1231236 A B R f h)). Qed.
Lemma lem1231239 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) : (term79 A B R f h) = (term66 A B R h f).
Proof. exact (eq_refl (term79 A B R f h)). Qed.
Lemma lem1231240 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) : ((term78 A B R f h) = (term79 A B R f h)) = ((term79 A B R f h) = (term66 A B R h f)).
Proof. exact (MK_COMB (@lem1231238 A B R f h) (@lem1231239 A B R h f)). Qed.
Lemma lem1231241 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) : (term79 A B R f h) = (term66 A B R h f).
Proof. exact (EQ_MP (@lem1231240 A B R h f) (@lem1231232 A B R f h)). Qed.
Lemma lem1231242 {A : Type'} : (@List.Forall A) = (@List.Forall A).
Proof. exact (eq_refl (@List.Forall A)). Qed.
Lemma lem1231243 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) : (term83 A B R f h) = (term68 A B R h f).
Proof. exact (MK_COMB (@lem1231242 A) (@lem1231241 A B R h f)). Qed.
Lemma lem1231244 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1231245 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) (t : list A) : (term84 A B R f h t) = (term69 A B R h f t).
Proof. exact (MK_COMB (@lem1231243 A B R h f) (@lem1231244 A t)). Qed.
Lemma lem1231246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231247 {A B : Type'} (R : type1402 B) (h : A) (f : A -> B) (t : list A) : (term85 A B R f h t) = (term71 A B R h f t).
Proof. exact (MK_COMB (@lem1231246) (@lem1231245 A B R h f t)). Qed.
Lemma lem1231248 {A B : Type'} (R : type1402 B) (f : A -> B) (t : list A) : (term10 A B R f t) = (term10 A B R f t).
Proof. exact (eq_refl (term10 A B R f t)). Qed.
Lemma lem1231249 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term75 A B h R f t) = (term72 A B h R f t).
Proof. exact (MK_COMB (@lem1231247 A B R h f t) (@lem1231248 A B R f t)). Qed.
Lemma lem1231252 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term15 A B R f h t) = (term72 A B h R f t).
Proof. exact (TRANS (@lem1231226 A B h R f t) (@lem1231249 A B h R f t)). Qed.
Lemma lem1231253 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : ((term14 A B R f h t) = (term15 A B R f h t)) = ((term72 A B h R f t) = (term72 A B h R f t)).
Proof. exact (MK_COMB (@lem1231222 A B h R f t h1) (@lem1231252 A B h R f t)). Qed.
Lemma lem1231255 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1231256 (x : Prop) : (x = x) = True.
Proof. exact (@lem1231255 Prop x). Qed.
Lemma lem1231257 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : ((term72 A B h R f t) = (term72 A B h R f t)) = True.
Proof. exact (@lem1231256 (term72 A B h R f t)). Qed.
Lemma lem1231260 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term86 A B h R f t) = (term86 A B h R f t).
Proof. exact (eq_refl (term86 A B h R f t)). Qed.
Lemma lem1231261 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term86 A B h R f t) = (((term72 A B h R f t) = (term72 A B h R f t)) = True).
Proof. exact (eq_refl (term86 A B h R f t)). Qed.
Lemma lem1231262 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term87 A B h R f t) = (term87 A B h R f t).
Proof. exact (eq_refl (term87 A B h R f t)). Qed.
Lemma lem1231263 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : ((term86 A B h R f t) = (term86 A B h R f t)) = ((term86 A B h R f t) = (((term72 A B h R f t) = (term72 A B h R f t)) = True)).
Proof. exact (MK_COMB (@lem1231262 A B h R f t) (@lem1231261 A B h R f t)). Qed.
Lemma lem1231264 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term86 A B h R f t) = (((term72 A B h R f t) = (term72 A B h R f t)) = True).
Proof. exact (eq_refl (term86 A B h R f t)). Qed.
Lemma lem1231265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1231266 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (term87 A B h R f t) = (term88 A B h R f t).
Proof. exact (MK_COMB (@lem1231265) (@lem1231264 A B h R f t)). Qed.
Lemma lem1231267 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (((term72 A B h R f t) = (term72 A B h R f t)) = True) = (((term72 A B h R f t) = (term72 A B h R f t)) = True).
Proof. exact (eq_refl (((term72 A B h R f t) = (term72 A B h R f t)) = True)). Qed.
Lemma lem1231268 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : ((term86 A B h R f t) = (((term72 A B h R f t) = (term72 A B h R f t)) = True)) = ((((term72 A B h R f t) = (term72 A B h R f t)) = True) = (((term72 A B h R f t) = (term72 A B h R f t)) = True)).
Proof. exact (MK_COMB (@lem1231266 A B h R f t) (@lem1231267 A B h R f t)). Qed.
Lemma lem1231269 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : ((term86 A B h R f t) = (term86 A B h R f t)) = ((((term72 A B h R f t) = (term72 A B h R f t)) = True) = (((term72 A B h R f t) = (term72 A B h R f t)) = True)).
Proof. exact (TRANS (@lem1231263 A B h R f t) (@lem1231268 A B h R f t)). Qed.
Lemma lem1231270 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : (((term72 A B h R f t) = (term72 A B h R f t)) = True) = (((term72 A B h R f t) = (term72 A B h R f t)) = True).
Proof. exact (EQ_MP (@lem1231269 A B h R f t) (@lem1231260 A B h R f t)). Qed.
Lemma lem1231271 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) : ((term72 A B h R f t) = (term72 A B h R f t)) = True.
Proof. exact (EQ_MP (@lem1231270 A B h R f t) (@lem1231257 A B h R f t)). Qed.
Lemma lem1231272 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : ((term14 A B R f h t) = (term15 A B R f h t)) = True.
Proof. exact (TRANS (@lem1231253 A B h R f t h1) (@lem1231271 A B h R f t)). Qed.
Lemma lem1231273 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : True = ((term14 A B R f h t) = (term15 A B R f h t)).
Proof. exact (SYM (@lem1231272 A B h R f t h1)). Qed.
Lemma lem1231274 {A B : Type'} (h : A) (R : type1402 B) (f : A -> B) (t : list A) (h1 : (term9 A B R f t) = (term10 A B R f t)) : (term14 A B R f h t) = (term15 A B R f h t).
Proof. exact (EQ_MP (@lem1231273 A B h R f t h1) (@lem0)). Qed.
Lemma lem1231275 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) (t : list A) : term17 A B R f h t.
Proof. exact (fun h0 : (term9 A B R f t) = (term10 A B R f t) => @lem1231274 A B h R f t h0). Qed.
Lemma lem1231280 {A B : Type'} (R : type1402 B) (f : A -> B) (h : A) : term21 A B R f h.
Proof. exact (fun t : list A => @lem1231275 A B R f h t). Qed.
Lemma lem1231285 {A B : Type'} (R : type1402 B) (f : A -> B) : term25 A B R f.
Proof. exact (fun h : A => @lem1231280 A B R f h). Qed.
Lemma lem1231286 {A B : Type'} (R : type1402 B) (f : A -> B) : term27 A B R f.
Proof. exact (conj (@lem1231154 A B R f) (@lem1231285 A B R f)). Qed.
Lemma lem1231287 {A B : Type'} (R : type1402 B) (f : A -> B) : term32 A B R f.
Proof. exact (@lem1231097 A B R f (@lem1231286 A B R f)). Qed.
Lemma lem1231292 {A B : Type'} (R : type1402 B) : term89 A B R.
Proof. exact (fun f : A -> B => @lem1231287 A B R f). Qed.
Lemma lem1231297 {A B : Type'} : term90 A B.
Proof. exact (fun R : type1402 B => @lem1231292 A B R). Qed.
