Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INTERS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INTERS_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3465954 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3465955 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3465956 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3465955 t1) (@lem3465954 t1)). Qed.
Lemma lem3465957 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3465956 t1 t2). Qed.
Lemma lem3465958 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3465959 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3465958 t1 t2) (@lem3465957 t1 t2)). Qed.
Lemma lem3465960 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3465959 t1 t2 t3). Qed.
Lemma lem3465961 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3465962 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3465961 t1 t2 t3) (@lem3465960 t1 t2 t3)). Qed.
Lemma lem3465963 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3465962 t1 t2 t3)). Qed.
Lemma lem3465964 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term7 _89465 _89481 f.
Proof. exact (@lem3453847 _89465 _89481 f). Qed.
Lemma lem3465965 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term7 _89465 _89481 f) = (term8 _89465 _89481 f).
Proof. exact (eq_refl (term7 _89465 _89481 f)). Qed.
Lemma lem3465966 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term8 _89465 _89481 f.
Proof. exact (EQ_MP (@lem3465965 _89465 _89481 f) (@lem3465964 _89465 _89481 f)). Qed.
Lemma lem3465967 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) : term9 _89465 _89481 f s.
Proof. exact (@lem3465966 _89465 _89481 f s). Qed.
Lemma lem3465968 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term9 _89465 _89481 f s) = ((term10 _89465 _89481 f s) = (term11 _89465 _89481 s f)).
Proof. exact (eq_refl (term9 _89465 _89481 f s)). Qed.
Lemma lem3466005 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term10 _89465 _89481 f s) = (term11 _89465 _89481 s f).
Proof. exact (EQ_MP (@lem3465968 _89465 _89481 s f) (@lem3465967 _89465 _89481 f s)). Qed.
Lemma lem3466006 {_89991 _90000 : Type'} (s : type686 _89991) (f : type678 _89991 _90000) : (term12 _89991 _90000 f s) = (term13 _89991 _90000 s f).
Proof. exact (@lem3466005 _90000 (_89991 -> Prop) s f). Qed.
Lemma lem3466007 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term14 _89991 _90000 f s) = (term15 _89991 _90000 s f).
Proof. exact (@lem3466006 _89991 _90000 s (@IMAGE _89991 _90000 f)). Qed.
Lemma lem3466018 {_89991 _90000 : Type'} (f : _89991 -> _90000) (s : type686 _89991) : (term16 _89991 _90000 f s) = (term16 _89991 _90000 f s).
Proof. exact (eq_refl (term16 _89991 _90000 f s)). Qed.
Lemma lem3466019 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : ((term17 _89991 _90000 f s) = (term14 _89991 _90000 f s)) = ((term17 _89991 _90000 f s) = (term15 _89991 _90000 s f)).
Proof. exact (MK_COMB (@lem3466018 _89991 _90000 f s) (@lem3466007 _89991 _90000 s f)). Qed.
Lemma lem3466022 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term18 _89991 _90000 s f) = (term18 _89991 _90000 s f).
Proof. exact (eq_refl (term18 _89991 _90000 s f)). Qed.
Lemma lem3466023 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term19 _89991 _90000 f s) = (term20 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466022 _89991 _90000 s f) (@lem3466019 _89991 _90000 s f)). Qed.
Lemma lem3466026 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term21 _89991 _90000 f) = (term22 _89991 _90000 f).
Proof. exact (fun_ext (fun s : type686 _89991 => @lem3466023 _89991 _90000 s f)). Qed.
Lemma lem3466027 {_89991 : Type'} : (@all ((_89991 -> Prop) -> Prop)) = (@all ((_89991 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_89991 -> Prop) -> Prop))). Qed.
Lemma lem3466028 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term23 _89991 _90000 f) = (term24 _89991 _90000 f).
Proof. exact (MK_COMB (@lem3466027 _89991) (@lem3466026 _89991 _90000 f)). Qed.
Lemma lem3466033 {_89991 _90000 : Type'} : (term25 _89991 _90000) = (term26 _89991 _90000).
Proof. exact (fun_ext (fun f : _89991 -> _90000 => @lem3466028 _89991 _90000 f)). Qed.
Lemma lem3466034 {_89991 _90000 : Type'} : (@all (_89991 -> _90000)) = (@all (_89991 -> _90000)).
Proof. exact (eq_refl (@all (_89991 -> _90000))). Qed.
Lemma lem3466035 {_89991 _90000 : Type'} : (term27 _89991 _90000) = (term28 _89991 _90000).
Proof. exact (MK_COMB (@lem3466034 _89991 _90000) (@lem3466033 _89991 _90000)). Qed.
Lemma lem3466040 {_89991 _90000 : Type'} : (term28 _89991 _90000) = (term27 _89991 _90000).
Proof. exact (SYM (@lem3466035 _89991 _90000)). Qed.
Lemma lem3466056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term29 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3466057 {_89991 : Type'} (s : type686 _89991) (t : type686 _89991) : (s = t) = (term30 _89991 s t).
Proof. exact (@lem3466056 (_89991 -> Prop) s t). Qed.
Lemma lem3466058 {_89991 : Type'} (s : type686 _89991) : (s = (@EMPTY (_89991 -> Prop))) = (term31 _89991 s).
Proof. exact (@lem3466057 _89991 s (@EMPTY (_89991 -> Prop))). Qed.
Lemma lem3466067 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3466068 {_89991 : Type'} (s : type686 _89991) : (term32 _89991 s) = (term33 _89991 s).
Proof. exact (MK_COMB (@lem3466067) (@lem3466058 _89991 s)). Qed.
Lemma lem3466069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466070 {_89991 : Type'} (s : type686 _89991) : (term34 _89991 s) = (term35 _89991 s).
Proof. exact (MK_COMB (@lem3466069) (@lem3466068 _89991 s)). Qed.
Lemma lem3466093 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term36 _89991 _90000 s f) = (term36 _89991 _90000 s f).
Proof. exact (eq_refl (term36 _89991 _90000 s f)). Qed.
Lemma lem3466094 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term37 _89991 _90000 s f) = (term38 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466070 _89991 s) (@lem3466093 _89991 _90000 s f)). Qed.
Lemma lem3466097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3466098 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term18 _89991 _90000 s f) = (term39 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466097) (@lem3466094 _89991 _90000 s f)). Qed.
Lemma lem3466102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term29 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3466103 {_90000 : Type'} (s : _90000 -> Prop) (t : _90000 -> Prop) : (s = t) = (term29 _90000 s t).
Proof. exact (@lem3466102 _90000 s t). Qed.
Lemma lem3466104 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : ((term17 _89991 _90000 f s) = (term15 _89991 _90000 s f)) = (term40 _89991 _90000 s f).
Proof. exact (@lem3466103 _90000 (term17 _89991 _90000 f s) (term15 _89991 _90000 s f)). Qed.
Lemma lem3466123 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term20 _89991 _90000 s f) = (term41 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466098 _89991 _90000 s f) (@lem3466104 _89991 _90000 s f)). Qed.
Lemma lem3466126 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term22 _89991 _90000 f) = (term42 _89991 _90000 f).
Proof. exact (fun_ext (fun s : type686 _89991 => @lem3466123 _89991 _90000 s f)). Qed.
Lemma lem3466127 {_89991 : Type'} : (@all ((_89991 -> Prop) -> Prop)) = (@all ((_89991 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_89991 -> Prop) -> Prop))). Qed.
Lemma lem3466128 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term24 _89991 _90000 f) = (term43 _89991 _90000 f).
Proof. exact (MK_COMB (@lem3466127 _89991) (@lem3466126 _89991 _90000 f)). Qed.
Lemma lem3466133 {_89991 _90000 : Type'} : (term26 _89991 _90000) = (term44 _89991 _90000).
Proof. exact (fun_ext (fun f : _89991 -> _90000 => @lem3466128 _89991 _90000 f)). Qed.
Lemma lem3466134 {_89991 _90000 : Type'} : (@all (_89991 -> _90000)) = (@all (_89991 -> _90000)).
Proof. exact (eq_refl (@all (_89991 -> _90000))). Qed.
Lemma lem3466135 {_89991 _90000 : Type'} : (term28 _89991 _90000) = (term45 _89991 _90000).
Proof. exact (MK_COMB (@lem3466134 _89991 _90000) (@lem3466133 _89991 _90000)). Qed.
Lemma lem3466140 {_89991 _90000 : Type'} : (term45 _89991 _90000) = (term28 _89991 _90000).
Proof. exact (SYM (@lem3466135 _89991 _90000)). Qed.
Lemma lem3466160 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466161 {_89991 : Type'} (P : type686 _89991) (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x P) = (P x).
Proof. exact (@lem3466160 (_89991 -> Prop) P x). Qed.
Lemma lem3466162 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x s) = (s x).
Proof. exact (@lem3466161 _89991 s x). Qed.
Lemma lem3466163 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3466164 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term46 _89991 x s) = (term47 _89991 s x).
Proof. exact (MK_COMB (@lem3466163) (@lem3466162 _89991 s x)). Qed.
Lemma lem3466166 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3466167 {_89991 : Type'} (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x (@EMPTY (_89991 -> Prop))) = False.
Proof. exact (@lem3466166 (_89991 -> Prop) x). Qed.
Lemma lem3466168 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : ((@IN (_89991 -> Prop) x s) = (@IN (_89991 -> Prop) x (@EMPTY (_89991 -> Prop)))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3466164 _89991 s x) (@lem3466167 _89991 x)). Qed.
Lemma lem3466170 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3466171 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : ((s x) = False) = (term48 _89991 s x).
Proof. exact (@lem3466170 (s x)). Qed.
Lemma lem3466172 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : ((@IN (_89991 -> Prop) x s) = (@IN (_89991 -> Prop) x (@EMPTY (_89991 -> Prop)))) = (term48 _89991 s x).
Proof. exact (TRANS (@lem3466168 _89991 s x) (@lem3466171 _89991 s x)). Qed.
Lemma lem3466173 {_89991 : Type'} (s : type686 _89991) : (term49 _89991 s) = (term50 _89991 s).
Proof. exact (fun_ext (fun x : _89991 -> Prop => @lem3466172 _89991 s x)). Qed.
Lemma lem3466174 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466175 {_89991 : Type'} (s : type686 _89991) : (term31 _89991 s) = (term51 _89991 s).
Proof. exact (MK_COMB (@lem3466174 _89991) (@lem3466173 _89991 s)). Qed.
Lemma lem3466180 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3466181 {_89991 : Type'} (s : type686 _89991) : (term33 _89991 s) = (term52 _89991 s).
Proof. exact (MK_COMB (@lem3466180) (@lem3466175 _89991 s)). Qed.
Lemma lem3466182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466183 {_89991 : Type'} (s : type686 _89991) : (term35 _89991 s) = (term53 _89991 s).
Proof. exact (MK_COMB (@lem3466182) (@lem3466181 _89991 s)). Qed.
Lemma lem3466197 {A : Type'} (s : type686 A) (x : A) : (term54 A x s) = (term55 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3466198 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term54 _89991 x s) = (term55 _89991 s x).
Proof. exact (@lem3466197 _89991 s x). Qed.
Lemma lem3466206 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466207 {_89991 : Type'} (P : type686 _89991) (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x P) = (P x).
Proof. exact (@lem3466206 (_89991 -> Prop) P x). Qed.
Lemma lem3466208 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (@IN (_89991 -> Prop) t s) = (s t).
Proof. exact (@lem3466207 _89991 s t). Qed.
Lemma lem3466209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466210 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term56 _89991 t s) = (term57 _89991 s t).
Proof. exact (MK_COMB (@lem3466209) (@lem3466208 _89991 s t)). Qed.
Lemma lem3466212 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466213 {_89991 : Type'} (P : _89991 -> Prop) (x : _89991) : (@IN _89991 x P) = (P x).
Proof. exact (@lem3466212 _89991 P x). Qed.
Lemma lem3466214 {_89991 : Type'} (t : _89991 -> Prop) (x : _89991) : (@IN _89991 x t) = (t x).
Proof. exact (@lem3466213 _89991 t x). Qed.
Lemma lem3466215 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term58 _89991 s x t) = (term59 _89991 s t x).
Proof. exact (MK_COMB (@lem3466210 _89991 s t) (@lem3466214 _89991 t x)). Qed.
Lemma lem3466218 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term60 _89991 s x) = (term61 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466215 _89991 s t x)). Qed.
Lemma lem3466219 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3466220 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term55 _89991 s x) = (term62 _89991 s x).
Proof. exact (MK_COMB (@lem3466219 _89991) (@lem3466218 _89991 s x)). Qed.
Lemma lem3466225 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term54 _89991 x s) = (term62 _89991 s x).
Proof. exact (TRANS (@lem3466198 _89991 s x) (@lem3466220 _89991 s x)). Qed.
Lemma lem3466226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466227 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term63 _89991 x s) = (term64 _89991 s x).
Proof. exact (MK_COMB (@lem3466226) (@lem3466225 _89991 s x)). Qed.
Lemma lem3466231 {A : Type'} (s : type686 A) (x : A) : (term54 A x s) = (term55 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3466232 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term54 _89991 x s) = (term55 _89991 s x).
Proof. exact (@lem3466231 _89991 s x). Qed.
Lemma lem3466233 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term54 _89991 y s) = (term55 _89991 s y).
Proof. exact (@lem3466232 _89991 s y). Qed.
Lemma lem3466241 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466242 {_89991 : Type'} (P : type686 _89991) (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x P) = (P x).
Proof. exact (@lem3466241 (_89991 -> Prop) P x). Qed.
Lemma lem3466243 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (@IN (_89991 -> Prop) t s) = (s t).
Proof. exact (@lem3466242 _89991 s t). Qed.
Lemma lem3466244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466245 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term56 _89991 t s) = (term57 _89991 s t).
Proof. exact (MK_COMB (@lem3466244) (@lem3466243 _89991 s t)). Qed.
Lemma lem3466247 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466248 {_89991 : Type'} (P : _89991 -> Prop) (x : _89991) : (@IN _89991 x P) = (P x).
Proof. exact (@lem3466247 _89991 P x). Qed.
Lemma lem3466249 {_89991 : Type'} (t : _89991 -> Prop) (y : _89991) : (@IN _89991 y t) = (t y).
Proof. exact (@lem3466248 _89991 t y). Qed.
Lemma lem3466250 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term58 _89991 s y t) = (term59 _89991 s t y).
Proof. exact (MK_COMB (@lem3466245 _89991 s t) (@lem3466249 _89991 t y)). Qed.
Lemma lem3466253 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term60 _89991 s y) = (term61 _89991 s y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466250 _89991 s t y)). Qed.
Lemma lem3466254 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3466255 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term55 _89991 s y) = (term62 _89991 s y).
Proof. exact (MK_COMB (@lem3466254 _89991) (@lem3466253 _89991 s y)). Qed.
Lemma lem3466260 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term54 _89991 y s) = (term62 _89991 s y).
Proof. exact (TRANS (@lem3466233 _89991 s y) (@lem3466255 _89991 s y)). Qed.
Lemma lem3466261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466262 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term63 _89991 y s) = (term64 _89991 s y).
Proof. exact (MK_COMB (@lem3466261) (@lem3466260 _89991 s y)). Qed.
Lemma lem3466265 {_89991 _90000 : Type'} (x : _89991) (f : _89991 -> _90000) (y : _89991) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3466266 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term65 _89991 _90000 s x f y) = (term66 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466262 _89991 s y) (@lem3466265 _89991 _90000 x f y)). Qed.
Lemma lem3466269 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term67 _89991 _90000 s x f y) = (term68 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466227 _89991 s x) (@lem3466266 _89991 _90000 s x f y)). Qed.
Lemma lem3466272 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3466273 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term69 _89991 _90000 s x f y) = (term70 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466272) (@lem3466269 _89991 _90000 s x f y)). Qed.
Lemma lem3466276 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3466277 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term71 _89991 _90000 s f x y) = (term72 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3466273 _89991 _90000 s x f y) (@lem3466276 _89991 x y)). Qed.
Lemma lem3466280 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term73 _89991 _90000 s f x) = (term74 _89991 _90000 s f x).
Proof. exact (fun_ext (fun y : _89991 => @lem3466277 _89991 _90000 s f x y)). Qed.
Lemma lem3466281 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3466282 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term75 _89991 _90000 s f x) = (term76 _89991 _90000 s f x).
Proof. exact (MK_COMB (@lem3466281 _89991) (@lem3466280 _89991 _90000 s f x)). Qed.
Lemma lem3466287 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term77 _89991 _90000 s f) = (term78 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _89991 => @lem3466282 _89991 _90000 s f x)). Qed.
Lemma lem3466288 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3466289 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term36 _89991 _90000 s f) = (term79 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466288 _89991) (@lem3466287 _89991 _90000 s f)). Qed.
Lemma lem3466294 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term38 _89991 _90000 s f) = (term80 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466183 _89991 s) (@lem3466289 _89991 _90000 s f)). Qed.
Lemma lem3466297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3466298 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term39 _89991 _90000 s f) = (term81 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466297) (@lem3466294 _89991 _90000 s f)). Qed.
Lemma lem3466306 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term82 A B y f s) = (term83 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3466307 {_89991 _90000 : Type'} (y : _90000) (f : _89991 -> _90000) (s : _89991 -> Prop) : (term82 _89991 _90000 y f s) = (term83 _89991 _90000 y f s).
Proof. exact (@lem3466306 _89991 _90000 y f s). Qed.
Lemma lem3466308 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term84 _89991 _90000 x f s) = (term85 _89991 _90000 x f s).
Proof. exact (@lem3466307 _89991 _90000 x f (@INTERS _89991 s)). Qed.
Lemma lem3466318 {A : Type'} (s : type686 A) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3466319 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term86 _89991 x s) = (term87 _89991 s x).
Proof. exact (@lem3466318 _89991 s x). Qed.
Lemma lem3466327 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466328 {_89991 : Type'} (P : type686 _89991) (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x P) = (P x).
Proof. exact (@lem3466327 (_89991 -> Prop) P x). Qed.
Lemma lem3466329 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (@IN (_89991 -> Prop) t s) = (s t).
Proof. exact (@lem3466328 _89991 s t). Qed.
Lemma lem3466330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3466331 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term88 _89991 t s) = (term89 _89991 s t).
Proof. exact (MK_COMB (@lem3466330) (@lem3466329 _89991 s t)). Qed.
Lemma lem3466333 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466334 {_89991 : Type'} (P : _89991 -> Prop) (x : _89991) : (@IN _89991 x P) = (P x).
Proof. exact (@lem3466333 _89991 P x). Qed.
Lemma lem3466335 {_89991 : Type'} (t : _89991 -> Prop) (x : _89991) : (@IN _89991 x t) = (t x).
Proof. exact (@lem3466334 _89991 t x). Qed.
Lemma lem3466336 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term90 _89991 s x t) = (term91 _89991 s t x).
Proof. exact (MK_COMB (@lem3466331 _89991 s t) (@lem3466335 _89991 t x)). Qed.
Lemma lem3466339 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term92 _89991 s x) = (term93 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466336 _89991 s t x)). Qed.
Lemma lem3466340 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466341 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term87 _89991 s x) = (term94 _89991 s x).
Proof. exact (MK_COMB (@lem3466340 _89991) (@lem3466339 _89991 s x)). Qed.
Lemma lem3466346 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term86 _89991 x s) = (term94 _89991 s x).
Proof. exact (TRANS (@lem3466319 _89991 s x) (@lem3466341 _89991 s x)). Qed.
Lemma lem3466347 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term95 _89991 _90000 x f x') = (term95 _89991 _90000 x f x').
Proof. exact (eq_refl (term95 _89991 _90000 x f x')). Qed.
Lemma lem3466348 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term96 _89991 _90000 x f x' s) = (term97 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3466347 _89991 _90000 x f x') (@lem3466346 _89991 s x')). Qed.
Lemma lem3466351 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term98 _89991 _90000 x f s) = (term99 _89991 _90000 x f s).
Proof. exact (fun_ext (fun x' : _89991 => @lem3466348 _89991 _90000 x f s x')). Qed.
Lemma lem3466352 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3466353 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term85 _89991 _90000 x f s) = (term100 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3466352 _89991) (@lem3466351 _89991 _90000 x f s)). Qed.
Lemma lem3466358 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term84 _89991 _90000 x f s) = (term100 _89991 _90000 x f s).
Proof. exact (TRANS (@lem3466308 _89991 _90000 x f s) (@lem3466353 _89991 _90000 x f s)). Qed.
Lemma lem3466359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3466360 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term101 _89991 _90000 x f s) = (term102 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3466359) (@lem3466358 _89991 _90000 x f s)). Qed.
Lemma lem3466362 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term103 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3466363 {_90000 : Type'} (p : _90000 -> Prop) (x : _90000) : (term103 _90000 x p) = (p x).
Proof. exact (@lem3466362 _90000 p x). Qed.
Lemma lem3466364 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _90000) : (term104 _89991 _90000 x s f) = (term105 _89991 _90000 s f x).
Proof. exact (@lem3466363 _90000 (term106 _89991 _90000 s f) x). Qed.
Lemma lem3466365 {_89991 _90000 : Type'} (s : type686 _89991) (y : _90000) (f : _89991 -> _90000) : (term105 _89991 _90000 s f y) = (term107 _89991 _90000 s y f).
Proof. exact (eq_refl (term105 _89991 _90000 s f y)). Qed.
Lemma lem3466366 {_90000 : Type'} (GEN_PVAR_48 : _90000) : (@SETSPEC _90000 GEN_PVAR_48) = (@SETSPEC _90000 GEN_PVAR_48).
Proof. exact (eq_refl (@SETSPEC _90000 GEN_PVAR_48)). Qed.
Lemma lem3466367 {_89991 _90000 : Type'} (GEN_PVAR_48 : _90000) (s : type686 _89991) (y : _90000) (f : _89991 -> _90000) : (term108 _89991 _90000 GEN_PVAR_48 s f y) = (term109 _89991 _90000 GEN_PVAR_48 s y f).
Proof. exact (MK_COMB (@lem3466366 _90000 GEN_PVAR_48) (@lem3466365 _89991 _90000 s y f)). Qed.
Lemma lem3466368 {_90000 : Type'} (y : _90000) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3466369 {_89991 _90000 : Type'} (GEN_PVAR_48 : _90000) (s : type686 _89991) (f : _89991 -> _90000) (y : _90000) : (term110 _89991 _90000 GEN_PVAR_48 s f y) = (term111 _89991 _90000 GEN_PVAR_48 s f y).
Proof. exact (MK_COMB (@lem3466367 _89991 _90000 GEN_PVAR_48 s y f) (@lem3466368 _90000 y)). Qed.
Lemma lem3466370 {_89991 _90000 : Type'} (GEN_PVAR_48 : _90000) (s : type686 _89991) (f : _89991 -> _90000) : (term112 _89991 _90000 GEN_PVAR_48 s f) = (term113 _89991 _90000 GEN_PVAR_48 s f).
Proof. exact (fun_ext (fun y : _90000 => @lem3466369 _89991 _90000 GEN_PVAR_48 s f y)). Qed.
Lemma lem3466371 {_90000 : Type'} : (@ex _90000) = (@ex _90000).
Proof. exact (eq_refl (@ex _90000)). Qed.
Lemma lem3466372 {_89991 _90000 : Type'} (GEN_PVAR_48 : _90000) (s : type686 _89991) (f : _89991 -> _90000) : (term114 _89991 _90000 GEN_PVAR_48 s f) = (term115 _89991 _90000 GEN_PVAR_48 s f).
Proof. exact (MK_COMB (@lem3466371 _90000) (@lem3466370 _89991 _90000 GEN_PVAR_48 s f)). Qed.
Lemma lem3466373 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term116 _89991 _90000 s f) = (term117 _89991 _90000 s f).
Proof. exact (fun_ext (fun GEN_PVAR_48 : _90000 => @lem3466372 _89991 _90000 GEN_PVAR_48 s f)). Qed.
Lemma lem3466374 {_90000 : Type'} : (@GSPEC _90000) = (@GSPEC _90000).
Proof. exact (eq_refl (@GSPEC _90000)). Qed.
Lemma lem3466375 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term118 _89991 _90000 s f) = (term15 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466374 _90000) (@lem3466373 _89991 _90000 s f)). Qed.
Lemma lem3466376 {_90000 : Type'} (x : _90000) : (@IN _90000 x) = (@IN _90000 x).
Proof. exact (eq_refl (@IN _90000 x)). Qed.
Lemma lem3466377 {_89991 _90000 : Type'} (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) : (term104 _89991 _90000 x s f) = (term119 _89991 _90000 x s f).
Proof. exact (MK_COMB (@lem3466376 _90000 x) (@lem3466375 _89991 _90000 s f)). Qed.
Lemma lem3466378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3466379 {_89991 _90000 : Type'} (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) : (term120 _89991 _90000 x s f) = (term121 _89991 _90000 x s f).
Proof. exact (MK_COMB (@lem3466378) (@lem3466377 _89991 _90000 x s f)). Qed.
Lemma lem3466380 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term105 _89991 _90000 s f x) = (term107 _89991 _90000 s x f).
Proof. exact (eq_refl (term105 _89991 _90000 s f x)). Qed.
Lemma lem3466381 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term104 _89991 _90000 x s f) = (term105 _89991 _90000 s f x)) = ((term119 _89991 _90000 x s f) = (term107 _89991 _90000 s x f)).
Proof. exact (MK_COMB (@lem3466379 _89991 _90000 x s f) (@lem3466380 _89991 _90000 s x f)). Qed.
Lemma lem3466382 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term119 _89991 _90000 x s f) = (term107 _89991 _90000 s x f).
Proof. exact (EQ_MP (@lem3466381 _89991 _90000 s x f) (@lem3466364 _89991 _90000 s f x)). Qed.
Lemma lem3466390 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466391 {_89991 : Type'} (P : type686 _89991) (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x P) = (P x).
Proof. exact (@lem3466390 (_89991 -> Prop) P x). Qed.
Lemma lem3466392 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (@IN (_89991 -> Prop) x s) = (s x).
Proof. exact (@lem3466391 _89991 s x). Qed.
Lemma lem3466393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3466394 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term88 _89991 x s) = (term89 _89991 s x).
Proof. exact (MK_COMB (@lem3466393) (@lem3466392 _89991 s x)). Qed.
Lemma lem3466396 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term82 A B y f s) = (term83 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3466397 {_89991 _90000 : Type'} (y : _90000) (f : _89991 -> _90000) (s : _89991 -> Prop) : (term82 _89991 _90000 y f s) = (term83 _89991 _90000 y f s).
Proof. exact (@lem3466396 _89991 _90000 y f s). Qed.
Lemma lem3466398 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term82 _89991 _90000 x f x') = (term83 _89991 _90000 x f x').
Proof. exact (@lem3466397 _89991 _90000 x f x'). Qed.
Lemma lem3466408 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3466409 {_89991 : Type'} (P : _89991 -> Prop) (x : _89991) : (@IN _89991 x P) = (P x).
Proof. exact (@lem3466408 _89991 P x). Qed.
Lemma lem3466410 {_89991 : Type'} (x : _89991 -> Prop) (x' : _89991) : (@IN _89991 x' x) = (x x').
Proof. exact (@lem3466409 _89991 x x'). Qed.
Lemma lem3466411 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term95 _89991 _90000 x f x') = (term95 _89991 _90000 x f x').
Proof. exact (eq_refl (term95 _89991 _90000 x f x')). Qed.
Lemma lem3466412 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term122 _89991 _90000 x f x'' x') = (term123 _89991 _90000 x f x' x'').
Proof. exact (MK_COMB (@lem3466411 _89991 _90000 x f x'') (@lem3466410 _89991 x' x'')). Qed.
Lemma lem3466415 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term124 _89991 _90000 x f x') = (term125 _89991 _90000 x f x').
Proof. exact (fun_ext (fun x'' : _89991 => @lem3466412 _89991 _90000 x f x' x'')). Qed.
Lemma lem3466416 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3466417 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term83 _89991 _90000 x f x') = (term126 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3466416 _89991) (@lem3466415 _89991 _90000 x f x')). Qed.
Lemma lem3466422 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term82 _89991 _90000 x f x') = (term126 _89991 _90000 x f x').
Proof. exact (TRANS (@lem3466398 _89991 _90000 x f x') (@lem3466417 _89991 _90000 x f x')). Qed.
Lemma lem3466423 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term127 _89991 _90000 s x f x') = (term128 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3466394 _89991 s x') (@lem3466422 _89991 _90000 x f x')). Qed.
Lemma lem3466426 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term129 _89991 _90000 s x f) = (term130 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3466423 _89991 _90000 s x f x')). Qed.
Lemma lem3466427 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466428 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term107 _89991 _90000 s x f) = (term131 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3466427 _89991) (@lem3466426 _89991 _90000 s x f)). Qed.
Lemma lem3466433 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term119 _89991 _90000 x s f) = (term131 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3466382 _89991 _90000 s x f) (@lem3466428 _89991 _90000 s x f)). Qed.
Lemma lem3466434 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term84 _89991 _90000 x f s) = (term119 _89991 _90000 x s f)) = ((term100 _89991 _90000 x f s) = (term131 _89991 _90000 s x f)).
Proof. exact (MK_COMB (@lem3466360 _89991 _90000 x f s) (@lem3466433 _89991 _90000 s x f)). Qed.
Lemma lem3466437 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term132 _89991 _90000 s f) = (term133 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _90000 => @lem3466434 _89991 _90000 s x f)). Qed.
Lemma lem3466438 {_90000 : Type'} : (@all _90000) = (@all _90000).
Proof. exact (eq_refl (@all _90000)). Qed.
Lemma lem3466439 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term40 _89991 _90000 s f) = (term134 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466438 _90000) (@lem3466437 _89991 _90000 s f)). Qed.
Lemma lem3466444 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term41 _89991 _90000 s f) = (term135 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466298 _89991 _90000 s f) (@lem3466439 _89991 _90000 s f)). Qed.
Lemma lem3466447 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term42 _89991 _90000 f) = (term136 _89991 _90000 f).
Proof. exact (fun_ext (fun s : type686 _89991 => @lem3466444 _89991 _90000 s f)). Qed.
Lemma lem3466448 {_89991 : Type'} : (@all ((_89991 -> Prop) -> Prop)) = (@all ((_89991 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_89991 -> Prop) -> Prop))). Qed.
Lemma lem3466449 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term43 _89991 _90000 f) = (term137 _89991 _90000 f).
Proof. exact (MK_COMB (@lem3466448 _89991) (@lem3466447 _89991 _90000 f)). Qed.
Lemma lem3466454 {_89991 _90000 : Type'} : (term44 _89991 _90000) = (term138 _89991 _90000).
Proof. exact (fun_ext (fun f : _89991 -> _90000 => @lem3466449 _89991 _90000 f)). Qed.
Lemma lem3466455 {_89991 _90000 : Type'} : (@all (_89991 -> _90000)) = (@all (_89991 -> _90000)).
Proof. exact (eq_refl (@all (_89991 -> _90000))). Qed.
Lemma lem3466456 {_89991 _90000 : Type'} : (term45 _89991 _90000) = (term139 _89991 _90000).
Proof. exact (MK_COMB (@lem3466455 _89991 _90000) (@lem3466454 _89991 _90000)). Qed.
Lemma lem3466461 {_89991 _90000 : Type'} : (term139 _89991 _90000) = (term45 _89991 _90000).
Proof. exact (SYM (@lem3466456 _89991 _90000)). Qed.
Lemma lem3466463 (p : Prop) : p = (term140 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3466464 {_89991 _90000 : Type'} : (term139 _89991 _90000) = (term141 _89991 _90000).
Proof. exact (@lem3466463 (term139 _89991 _90000)). Qed.
Lemma lem3466465 {_89991 _90000 : Type'} : (term141 _89991 _90000) = (term139 _89991 _90000).
Proof. exact (SYM (@lem3466464 _89991 _90000)). Qed.
Lemma lem3466466 {_89991 _90000 : Type'} (h1 : term142 _89991 _90000) : term142 _89991 _90000.
Proof. exact (h1). Qed.
Lemma lem3466469 {_89991 _90000 : Type'} (h1 : term141 _89991 _90000) : term141 _89991 _90000.
Proof. exact (h1). Qed.
Lemma lem3466470 {_89991 _90000 : Type'} : term143 _89991 _90000.
Proof. exact (fun h0 : term141 _89991 _90000 => @lem3466469 _89991 _90000 h0). Qed.
Lemma lem3466471 {_89991 _90000 : Type'} (h1 : term143 _89991 _90000) : term143 _89991 _90000.
Proof. exact (h1). Qed.
Lemma lem3466472 {_89991 _90000 : Type'} (h1 : term141 _89991 _90000) : term141 _89991 _90000.
Proof. exact (h1). Qed.
Lemma lem3466473 {_89991 _90000 : Type'} (h1 : term141 _89991 _90000) (h2 : term143 _89991 _90000) : term141 _89991 _90000.
Proof. exact (@lem3466471 _89991 _90000 h2 (@lem3466472 _89991 _90000 h1)). Qed.
Lemma lem3466474 {_89991 _90000 : Type'} (h1 : term141 _89991 _90000) : term144 _89991 _90000.
Proof. exact (fun h0 : term143 _89991 _90000 => @lem3466473 _89991 _90000 h1 h0). Qed.
Lemma lem3466475 {_89991 _90000 : Type'} (h1 : term143 _89991 _90000) : term143 _89991 _90000.
Proof. exact (h1). Qed.
Lemma lem3466476 {_89991 _90000 : Type'} (h1 : term141 _89991 _90000) (h2 : term143 _89991 _90000) : term141 _89991 _90000.
Proof. exact (@lem3466474 _89991 _90000 h1 (@lem3466475 _89991 _90000 h2)). Qed.
Lemma lem3466477 {_89991 _90000 : Type'} (h1 : term143 _89991 _90000) : term143 _89991 _90000.
Proof. exact (fun h0 : term141 _89991 _90000 => @lem3466476 _89991 _90000 h0 h1). Qed.
Lemma lem3466478 {_89991 _90000 : Type'} : term145 _89991 _90000.
Proof. exact (fun h0 : term143 _89991 _90000 => @lem3466477 _89991 _90000 h0). Qed.
Lemma lem3466481 {_89991 _90000 : Type'} : term143 _89991 _90000.
Proof. exact (@lem3466478 _89991 _90000 (@lem3466470 _89991 _90000)). Qed.
Lemma lem3466482 {_89991 _90000 : Type'} : term143 _89991 _90000.
Proof. exact (@lem3466481 _89991 _90000). Qed.
Lemma lem3466484 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3466485 {_89991 _90000 : Type'} : (term141 _89991 _90000) = (term146 _89991 _90000).
Proof. exact (@lem3466484 (term142 _89991 _90000)). Qed.
Lemma lem3466487 (t : Prop) : (term147 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3466488 {_89991 _90000 : Type'} : (term146 _89991 _90000) = (term139 _89991 _90000).
Proof. exact (@lem3466487 (term139 _89991 _90000)). Qed.
Lemma lem3466683 {_89991 _90000 : Type'} : (term141 _89991 _90000) = (term139 _89991 _90000).
Proof. exact (TRANS (@lem3466485 _89991 _90000) (@lem3466488 _89991 _90000)). Qed.
Lemma lem3466688 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term123 _89991 _90000 x f x' x'') = (term123 _89991 _90000 x f x' x'').
Proof. exact (eq_refl (term123 _89991 _90000 x f x' x'')). Qed.
Lemma lem3466689 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term125 _89991 _90000 x f x') = (term125 _89991 _90000 x f x').
Proof. exact (fun_ext (fun x'' : _89991 => @lem3466688 _89991 _90000 x f x' x'')). Qed.
Lemma lem3466690 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3466691 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term126 _89991 _90000 x f x') = (term126 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3466690 _89991) (@lem3466689 _89991 _90000 x f x')). Qed.
Lemma lem3466694 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term89 _89991 s x) = (term89 _89991 s x).
Proof. exact (eq_refl (term89 _89991 s x)). Qed.
Lemma lem3466695 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term128 _89991 _90000 s x f x') = (term128 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3466694 _89991 s x') (@lem3466691 _89991 _90000 x f x')). Qed.
Lemma lem3466696 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term130 _89991 _90000 s x f) = (term130 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3466695 _89991 _90000 s x f x')). Qed.
Lemma lem3466697 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466698 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term131 _89991 _90000 s x f) = (term131 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3466697 _89991) (@lem3466696 _89991 _90000 s x f)). Qed.
Lemma lem3466703 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term91 _89991 s t x) = (term91 _89991 s t x).
Proof. exact (eq_refl (term91 _89991 s t x)). Qed.
Lemma lem3466704 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term93 _89991 s x) = (term93 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466703 _89991 s t x)). Qed.
Lemma lem3466705 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466706 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term94 _89991 s x) = (term94 _89991 s x).
Proof. exact (MK_COMB (@lem3466705 _89991) (@lem3466704 _89991 s x)). Qed.
Lemma lem3466709 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term95 _89991 _90000 x f x') = (term95 _89991 _90000 x f x').
Proof. exact (eq_refl (term95 _89991 _90000 x f x')). Qed.
Lemma lem3466710 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term97 _89991 _90000 x f s x') = (term97 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3466709 _89991 _90000 x f x') (@lem3466706 _89991 s x')). Qed.
Lemma lem3466711 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term99 _89991 _90000 x f s) = (term99 _89991 _90000 x f s).
Proof. exact (fun_ext (fun x' : _89991 => @lem3466710 _89991 _90000 x f s x')). Qed.
Lemma lem3466712 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3466713 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term100 _89991 _90000 x f s) = (term100 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3466712 _89991) (@lem3466711 _89991 _90000 x f s)). Qed.
Lemma lem3466714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3466715 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term102 _89991 _90000 x f s) = (term102 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3466714) (@lem3466713 _89991 _90000 x f s)). Qed.
Lemma lem3466716 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term100 _89991 _90000 x f s) = (term131 _89991 _90000 s x f)) = ((term100 _89991 _90000 x f s) = (term131 _89991 _90000 s x f)).
Proof. exact (MK_COMB (@lem3466715 _89991 _90000 x f s) (@lem3466698 _89991 _90000 s x f)). Qed.
Lemma lem3466717 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term133 _89991 _90000 s f) = (term133 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _90000 => @lem3466716 _89991 _90000 s x f)). Qed.
Lemma lem3466718 {_90000 : Type'} : (@all _90000) = (@all _90000).
Proof. exact (eq_refl (@all _90000)). Qed.
Lemma lem3466719 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term134 _89991 _90000 s f) = (term134 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466718 _90000) (@lem3466717 _89991 _90000 s f)). Qed.
Lemma lem3466720 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3466721 {_89991 _90000 : Type'} (x : _89991) (f : _89991 -> _90000) (y : _89991) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3466726 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term59 _89991 s t y) = (term59 _89991 s t y).
Proof. exact (eq_refl (term59 _89991 s t y)). Qed.
Lemma lem3466727 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term61 _89991 s y) = (term61 _89991 s y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466726 _89991 s t y)). Qed.
Lemma lem3466728 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3466729 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term62 _89991 s y) = (term62 _89991 s y).
Proof. exact (MK_COMB (@lem3466728 _89991) (@lem3466727 _89991 s y)). Qed.
Lemma lem3466730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466731 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term64 _89991 s y) = (term64 _89991 s y).
Proof. exact (MK_COMB (@lem3466730) (@lem3466729 _89991 s y)). Qed.
Lemma lem3466732 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term66 _89991 _90000 s x f y) = (term66 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466731 _89991 s y) (@lem3466721 _89991 _90000 x f y)). Qed.
Lemma lem3466737 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term59 _89991 s t x) = (term59 _89991 s t x).
Proof. exact (eq_refl (term59 _89991 s t x)). Qed.
Lemma lem3466738 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term61 _89991 s x) = (term61 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466737 _89991 s t x)). Qed.
Lemma lem3466739 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3466740 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term62 _89991 s x) = (term62 _89991 s x).
Proof. exact (MK_COMB (@lem3466739 _89991) (@lem3466738 _89991 s x)). Qed.
Lemma lem3466741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466742 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term64 _89991 s x) = (term64 _89991 s x).
Proof. exact (MK_COMB (@lem3466741) (@lem3466740 _89991 s x)). Qed.
Lemma lem3466743 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term68 _89991 _90000 s x f y) = (term68 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466742 _89991 s x) (@lem3466732 _89991 _90000 s x f y)). Qed.
Lemma lem3466744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3466745 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term70 _89991 _90000 s x f y) = (term70 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466744) (@lem3466743 _89991 _90000 s x f y)). Qed.
Lemma lem3466746 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term72 _89991 _90000 s f x y) = (term72 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3466745 _89991 _90000 s x f y) (@lem3466720 _89991 x y)). Qed.
Lemma lem3466747 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term74 _89991 _90000 s f x) = (term74 _89991 _90000 s f x).
Proof. exact (fun_ext (fun y : _89991 => @lem3466746 _89991 _90000 s f x y)). Qed.
Lemma lem3466748 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3466749 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term76 _89991 _90000 s f x) = (term76 _89991 _90000 s f x).
Proof. exact (MK_COMB (@lem3466748 _89991) (@lem3466747 _89991 _90000 s f x)). Qed.
Lemma lem3466750 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term78 _89991 _90000 s f) = (term78 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _89991 => @lem3466749 _89991 _90000 s f x)). Qed.
Lemma lem3466751 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3466752 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term79 _89991 _90000 s f) = (term79 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466751 _89991) (@lem3466750 _89991 _90000 s f)). Qed.
Lemma lem3466755 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term48 _89991 s x) = (term48 _89991 s x).
Proof. exact (eq_refl (term48 _89991 s x)). Qed.
Lemma lem3466756 {_89991 : Type'} (s : type686 _89991) : (term50 _89991 s) = (term50 _89991 s).
Proof. exact (fun_ext (fun x : _89991 -> Prop => @lem3466755 _89991 s x)). Qed.
Lemma lem3466757 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466758 {_89991 : Type'} (s : type686 _89991) : (term51 _89991 s) = (term51 _89991 s).
Proof. exact (MK_COMB (@lem3466757 _89991) (@lem3466756 _89991 s)). Qed.
Lemma lem3466759 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3466760 {_89991 : Type'} (s : type686 _89991) : (term52 _89991 s) = (term52 _89991 s).
Proof. exact (MK_COMB (@lem3466759) (@lem3466758 _89991 s)). Qed.
Lemma lem3466761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466762 {_89991 : Type'} (s : type686 _89991) : (term53 _89991 s) = (term53 _89991 s).
Proof. exact (MK_COMB (@lem3466761) (@lem3466760 _89991 s)). Qed.
Lemma lem3466763 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term80 _89991 _90000 s f) = (term80 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466762 _89991 s) (@lem3466752 _89991 _90000 s f)). Qed.
Lemma lem3466764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3466765 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term81 _89991 _90000 s f) = (term81 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466764) (@lem3466763 _89991 _90000 s f)). Qed.
Lemma lem3466766 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term135 _89991 _90000 s f) = (term135 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466765 _89991 _90000 s f) (@lem3466719 _89991 _90000 s f)). Qed.
Lemma lem3466767 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term136 _89991 _90000 f) = (term136 _89991 _90000 f).
Proof. exact (fun_ext (fun s : type686 _89991 => @lem3466766 _89991 _90000 s f)). Qed.
Lemma lem3466768 {_89991 : Type'} : (@all ((_89991 -> Prop) -> Prop)) = (@all ((_89991 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_89991 -> Prop) -> Prop))). Qed.
Lemma lem3466769 {_89991 _90000 : Type'} (f : _89991 -> _90000) : (term137 _89991 _90000 f) = (term137 _89991 _90000 f).
Proof. exact (MK_COMB (@lem3466768 _89991) (@lem3466767 _89991 _90000 f)). Qed.
Lemma lem3466770 {_89991 _90000 : Type'} : (term138 _89991 _90000) = (term138 _89991 _90000).
Proof. exact (fun_ext (fun f : _89991 -> _90000 => @lem3466769 _89991 _90000 f)). Qed.
Lemma lem3466771 {_89991 _90000 : Type'} : (@all (_89991 -> _90000)) = (@all (_89991 -> _90000)).
Proof. exact (eq_refl (@all (_89991 -> _90000))). Qed.
Lemma lem3466772 {_89991 _90000 : Type'} : (term139 _89991 _90000) = (term139 _89991 _90000).
Proof. exact (MK_COMB (@lem3466771 _89991 _90000) (@lem3466770 _89991 _90000)). Qed.
Lemma lem3466869 {_89991 _90000 : Type'} : (term141 _89991 _90000) = (term139 _89991 _90000).
Proof. exact (TRANS (@lem3466683 _89991 _90000) (@lem3466772 _89991 _90000)). Qed.
Lemma lem3466870 {_89991 _90000 : Type'} : (term139 _89991 _90000) = (term141 _89991 _90000).
Proof. exact (SYM (@lem3466869 _89991 _90000)). Qed.
Lemma lem3466871 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (h1 : term80 _89991 _90000 s f) : term80 _89991 _90000 s f.
Proof. exact (h1). Qed.
Lemma lem3466873 (p : Prop) : p = (term140 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3466874 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term100 _89991 _90000 x f s) = (term131 _89991 _90000 s x f)) = (term148 _89991 _90000 s x f).
Proof. exact (@lem3466873 ((term100 _89991 _90000 x f s) = (term131 _89991 _90000 s x f))). Qed.
Lemma lem3466875 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term148 _89991 _90000 s x f) = ((term100 _89991 _90000 x f s) = (term131 _89991 _90000 s x f)).
Proof. exact (SYM (@lem3466874 _89991 _90000 s x f)). Qed.
Lemma lem3466876 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (h1 : term149 _89991 _90000 s x f) : term149 _89991 _90000 s x f.
Proof. exact (h1). Qed.
Lemma lem3466879 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term150 _89991 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3466880 {_89991 : Type'} (P : type686 _89991) : (term151 _89991 P) = (term152 _89991 P).
Proof. exact (@lem18392 (_89991 -> Prop) P). Qed.
Lemma lem3466881 {_89991 : Type'} (s : type686 _89991) : (term52 _89991 s) = (term153 _89991 s).
Proof. exact (@lem3466880 _89991 (term50 _89991 s)). Qed.
Lemma lem3466882 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term154 _89991 s x) = (term48 _89991 s x).
Proof. exact (eq_refl (term154 _89991 s x)). Qed.
Lemma lem3466883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3466884 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term155 _89991 s x) = (term150 _89991 s x).
Proof. exact (MK_COMB (@lem3466883) (@lem3466882 _89991 s x)). Qed.
Lemma lem3466885 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term155 _89991 s x) = (s x).
Proof. exact (TRANS (@lem3466884 _89991 s x) (@lem3466879 _89991 s x)). Qed.
Lemma lem3466886 {_89991 : Type'} (s : type686 _89991) : (term156 _89991 s) = (term157 _89991 s).
Proof. exact (fun_ext (fun x : _89991 -> Prop => @lem3466885 _89991 s x)). Qed.
Lemma lem3466887 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3466888 {_89991 : Type'} (s : type686 _89991) : (term153 _89991 s) = (term158 _89991 s).
Proof. exact (MK_COMB (@lem3466887 _89991) (@lem3466886 _89991 s)). Qed.
Lemma lem3466889 {_89991 : Type'} (s : type686 _89991) : (term52 _89991 s) = (term158 _89991 s).
Proof. exact (TRANS (@lem3466881 _89991 s) (@lem3466888 _89991 s)). Qed.
Lemma lem3466896 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term159 _89991 s t x) = (term160 _89991 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3466897 {_89991 : Type'} (P : type686 _89991) : (term161 _89991 P) = (term51 _89991 P).
Proof. exact (@lem18394 (_89991 -> Prop) P). Qed.
Lemma lem3466898 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term162 _89991 s x) = (term163 _89991 s x).
Proof. exact (@lem3466897 _89991 (term61 _89991 s x)). Qed.
Lemma lem3466899 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term164 _89991 s x t) = (term59 _89991 s t x).
Proof. exact (eq_refl (term164 _89991 s x t)). Qed.
Lemma lem3466900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3466901 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term165 _89991 s x t) = (term159 _89991 s t x).
Proof. exact (MK_COMB (@lem3466900) (@lem3466899 _89991 s t x)). Qed.
Lemma lem3466902 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term165 _89991 s x t) = (term160 _89991 s t x).
Proof. exact (TRANS (@lem3466901 _89991 s t x) (@lem3466896 _89991 s t x)). Qed.
Lemma lem3466903 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term166 _89991 s x) = (term167 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466902 _89991 s t x)). Qed.
Lemma lem3466904 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466905 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term163 _89991 s x) = (term168 _89991 s x).
Proof. exact (MK_COMB (@lem3466904 _89991) (@lem3466903 _89991 s x)). Qed.
Lemma lem3466906 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term162 _89991 s x) = (term168 _89991 s x).
Proof. exact (TRANS (@lem3466898 _89991 s x) (@lem3466905 _89991 s x)). Qed.
Lemma lem3466913 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term159 _89991 s t y) = (term160 _89991 s t y).
Proof. exact (@lem17045 (s t) (t y)). Qed.
Lemma lem3466914 {_89991 : Type'} (P : type686 _89991) : (term161 _89991 P) = (term51 _89991 P).
Proof. exact (@lem18394 (_89991 -> Prop) P). Qed.
Lemma lem3466915 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term162 _89991 s y) = (term163 _89991 s y).
Proof. exact (@lem3466914 _89991 (term61 _89991 s y)). Qed.
Lemma lem3466916 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term164 _89991 s y t) = (term59 _89991 s t y).
Proof. exact (eq_refl (term164 _89991 s y t)). Qed.
Lemma lem3466917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3466918 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term165 _89991 s y t) = (term159 _89991 s t y).
Proof. exact (MK_COMB (@lem3466917) (@lem3466916 _89991 s t y)). Qed.
Lemma lem3466919 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term165 _89991 s y t) = (term160 _89991 s t y).
Proof. exact (TRANS (@lem3466918 _89991 s t y) (@lem3466913 _89991 s t y)). Qed.
Lemma lem3466920 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term166 _89991 s y) = (term167 _89991 s y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3466919 _89991 s t y)). Qed.
Lemma lem3466921 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3466922 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term163 _89991 s y) = (term168 _89991 s y).
Proof. exact (MK_COMB (@lem3466921 _89991) (@lem3466920 _89991 s y)). Qed.
Lemma lem3466923 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term162 _89991 s y) = (term168 _89991 s y).
Proof. exact (TRANS (@lem3466915 _89991 s y) (@lem3466922 _89991 s y)). Qed.
Lemma lem3466924 {_89991 _90000 : Type'} (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term169 _89991 _90000 x f y) = (term169 _89991 _90000 x f y).
Proof. exact (eq_refl (term169 _89991 _90000 x f y)). Qed.
Lemma lem3466925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3466926 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term170 _89991 s y) = (term171 _89991 s y).
Proof. exact (MK_COMB (@lem3466925) (@lem3466923 _89991 s y)). Qed.
Lemma lem3466927 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term172 _89991 _90000 s x f y) = (term173 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466926 _89991 s y) (@lem3466924 _89991 _90000 x f y)). Qed.
Lemma lem3466928 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term174 _89991 _90000 s x f y) = (term172 _89991 _90000 s x f y).
Proof. exact (@lem17045 (term62 _89991 s y) ((f x) = (f y))). Qed.
Lemma lem3466929 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term174 _89991 _90000 s x f y) = (term173 _89991 _90000 s x f y).
Proof. exact (TRANS (@lem3466928 _89991 _90000 s x f y) (@lem3466927 _89991 _90000 s x f y)). Qed.
Lemma lem3466930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3466931 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term170 _89991 s x) = (term171 _89991 s x).
Proof. exact (MK_COMB (@lem3466930) (@lem3466906 _89991 s x)). Qed.
Lemma lem3466932 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term175 _89991 _90000 s x f y) = (term176 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466931 _89991 s x) (@lem3466929 _89991 _90000 s x f y)). Qed.
Lemma lem3466933 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term177 _89991 _90000 s x f y) = (term175 _89991 _90000 s x f y).
Proof. exact (@lem17045 (term62 _89991 s x) (term66 _89991 _90000 s x f y)). Qed.
Lemma lem3466934 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term177 _89991 _90000 s x f y) = (term176 _89991 _90000 s x f y).
Proof. exact (TRANS (@lem3466933 _89991 _90000 s x f y) (@lem3466932 _89991 _90000 s x f y)). Qed.
Lemma lem3466935 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3466936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3466937 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term178 _89991 _90000 s x f y) = (term179 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3466936) (@lem3466934 _89991 _90000 s x f y)). Qed.
Lemma lem3466938 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term180 _89991 _90000 s f x y) = (term181 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3466937 _89991 _90000 s x f y) (@lem3466935 _89991 x y)). Qed.
Lemma lem3466939 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term72 _89991 _90000 s f x y) = (term180 _89991 _90000 s f x y).
Proof. exact (@lem17265 (term68 _89991 _90000 s x f y) (x = y)). Qed.
Lemma lem3466940 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term72 _89991 _90000 s f x y) = (term181 _89991 _90000 s f x y).
Proof. exact (TRANS (@lem3466939 _89991 _90000 s f x y) (@lem3466938 _89991 _90000 s f x y)). Qed.
Lemma lem3466941 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term74 _89991 _90000 s f x) = (term182 _89991 _90000 s f x).
Proof. exact (fun_ext (fun y : _89991 => @lem3466940 _89991 _90000 s f x y)). Qed.
Lemma lem3466942 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3466943 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term76 _89991 _90000 s f x) = (term183 _89991 _90000 s f x).
Proof. exact (MK_COMB (@lem3466942 _89991) (@lem3466941 _89991 _90000 s f x)). Qed.
Lemma lem3466944 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term78 _89991 _90000 s f) = (term184 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _89991 => @lem3466943 _89991 _90000 s f x)). Qed.
Lemma lem3466945 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3466946 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term79 _89991 _90000 s f) = (term185 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466945 _89991) (@lem3466944 _89991 _90000 s f)). Qed.
Lemma lem3466947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3466948 {_89991 : Type'} (s : type686 _89991) : (term53 _89991 s) = (term186 _89991 s).
Proof. exact (MK_COMB (@lem3466947) (@lem3466889 _89991 s)). Qed.
Lemma lem3466949 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term80 _89991 _90000 s f) = (term187 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3466948 _89991 s) (@lem3466946 _89991 _90000 s f)). Qed.
Lemma lem3467104 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3467105 {_89991 : Type'} (P : type686 _89991) (Q : Prop) : (term190 _89991 P Q) = (term191 _89991 P Q).
Proof. exact (@lem3467104 (_89991 -> Prop) P Q). Qed.
Lemma lem3467107 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term187 _89991 _90000 s f) = (term192 _89991 _90000 s f).
Proof. exact (@lem3467105 _89991 s (term185 _89991 _90000 s f)). Qed.
Lemma lem3467108 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term80 _89991 _90000 s f) = (term192 _89991 _90000 s f).
Proof. exact (TRANS (@lem3466949 _89991 _90000 s f) (@lem3467107 _89991 _90000 s f)). Qed.
Lemma lem3467109 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (h1 : term80 _89991 _90000 s f) : term192 _89991 _90000 s f.
Proof. exact (EQ_MP (@lem3467108 _89991 _90000 s f) (@lem3466871 _89991 _90000 s f h1)). Qed.
Lemma lem3467120 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term193 _89991 s t x) = (term194 _89991 s t x).
Proof. exact (@lem17362 (s t) (t x)). Qed.
Lemma lem3467125 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term91 _89991 s t x) = (term195 _89991 s t x).
Proof. exact (@lem17265 (s t) (t x)). Qed.
Lemma lem3467126 {_89991 : Type'} (P : type686 _89991) : (term151 _89991 P) = (term152 _89991 P).
Proof. exact (@lem18392 (_89991 -> Prop) P). Qed.
Lemma lem3467127 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term196 _89991 s x) = (term197 _89991 s x).
Proof. exact (@lem3467126 _89991 (term93 _89991 s x)). Qed.
Lemma lem3467128 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term198 _89991 s x t) = (term91 _89991 s t x).
Proof. exact (eq_refl (term198 _89991 s x t)). Qed.
Lemma lem3467129 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467130 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term199 _89991 s x t) = (term193 _89991 s t x).
Proof. exact (MK_COMB (@lem3467129) (@lem3467128 _89991 s t x)). Qed.
Lemma lem3467131 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term199 _89991 s x t) = (term194 _89991 s t x).
Proof. exact (TRANS (@lem3467130 _89991 s t x) (@lem3467120 _89991 s t x)). Qed.
Lemma lem3467132 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term200 _89991 s x) = (term201 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3467131 _89991 s t x)). Qed.
Lemma lem3467133 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467134 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term197 _89991 s x) = (term202 _89991 s x).
Proof. exact (MK_COMB (@lem3467133 _89991) (@lem3467132 _89991 s x)). Qed.
Lemma lem3467135 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term196 _89991 s x) = (term202 _89991 s x).
Proof. exact (TRANS (@lem3467127 _89991 s x) (@lem3467134 _89991 s x)). Qed.
Lemma lem3467136 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term93 _89991 s x) = (term203 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3467125 _89991 s t x)). Qed.
Lemma lem3467137 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3467138 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term94 _89991 s x) = (term204 _89991 s x).
Proof. exact (MK_COMB (@lem3467137 _89991) (@lem3467136 _89991 s x)). Qed.
Lemma lem3467140 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term205 _89991 _90000 x f x') = (term205 _89991 _90000 x f x').
Proof. exact (eq_refl (term205 _89991 _90000 x f x')). Qed.
Lemma lem3467141 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term206 _89991 _90000 x f s x') = (term207 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467140 _89991 _90000 x f x') (@lem3467135 _89991 s x')). Qed.
Lemma lem3467142 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term208 _89991 _90000 x f s x') = (term206 _89991 _90000 x f s x').
Proof. exact (@lem17045 (x = (f x')) (term94 _89991 s x')). Qed.
Lemma lem3467143 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term208 _89991 _90000 x f s x') = (term207 _89991 _90000 x f s x').
Proof. exact (TRANS (@lem3467142 _89991 _90000 x f s x') (@lem3467141 _89991 _90000 x f s x')). Qed.
Lemma lem3467145 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term95 _89991 _90000 x f x') = (term95 _89991 _90000 x f x').
Proof. exact (eq_refl (term95 _89991 _90000 x f x')). Qed.
Lemma lem3467146 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term97 _89991 _90000 x f s x') = (term209 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467145 _89991 _90000 x f x') (@lem3467138 _89991 s x')). Qed.
Lemma lem3467147 {_89991 : Type'} (P : _89991 -> Prop) : (term210 _89991 P) = (term211 _89991 P).
Proof. exact (@lem18394 _89991 P). Qed.
Lemma lem3467148 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term212 _89991 _90000 x f s) = (term213 _89991 _90000 x f s).
Proof. exact (@lem3467147 _89991 (term99 _89991 _90000 x f s)). Qed.
Lemma lem3467149 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term214 _89991 _90000 x f s x') = (term97 _89991 _90000 x f s x').
Proof. exact (eq_refl (term214 _89991 _90000 x f s x')). Qed.
Lemma lem3467150 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467151 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term215 _89991 _90000 x f s x') = (term208 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467150) (@lem3467149 _89991 _90000 x f s x')). Qed.
Lemma lem3467152 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term215 _89991 _90000 x f s x') = (term207 _89991 _90000 x f s x').
Proof. exact (TRANS (@lem3467151 _89991 _90000 x f s x') (@lem3467143 _89991 _90000 x f s x')). Qed.
Lemma lem3467153 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term216 _89991 _90000 x f s) = (term217 _89991 _90000 x f s).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467152 _89991 _90000 x f s x')). Qed.
Lemma lem3467154 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3467155 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term213 _89991 _90000 x f s) = (term218 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467154 _89991) (@lem3467153 _89991 _90000 x f s)). Qed.
Lemma lem3467156 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term212 _89991 _90000 x f s) = (term218 _89991 _90000 x f s).
Proof. exact (TRANS (@lem3467148 _89991 _90000 x f s) (@lem3467155 _89991 _90000 x f s)). Qed.
Lemma lem3467157 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term99 _89991 _90000 x f s) = (term219 _89991 _90000 x f s).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467146 _89991 _90000 x f s x')). Qed.
Lemma lem3467158 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467159 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term100 _89991 _90000 x f s) = (term220 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467158 _89991) (@lem3467157 _89991 _90000 x f s)). Qed.
Lemma lem3467170 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term221 _89991 _90000 x f x' x'') = (term222 _89991 _90000 x f x' x'').
Proof. exact (@lem17045 (x = (f x'')) (x' x'')). Qed.
Lemma lem3467173 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term123 _89991 _90000 x f x' x'') = (term123 _89991 _90000 x f x' x'').
Proof. exact (eq_refl (term123 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467174 {_89991 : Type'} (P : _89991 -> Prop) : (term210 _89991 P) = (term211 _89991 P).
Proof. exact (@lem18394 _89991 P). Qed.
Lemma lem3467175 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term223 _89991 _90000 x f x') = (term224 _89991 _90000 x f x').
Proof. exact (@lem3467174 _89991 (term125 _89991 _90000 x f x')). Qed.
Lemma lem3467176 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term225 _89991 _90000 x f x' x'') = (term123 _89991 _90000 x f x' x'').
Proof. exact (eq_refl (term225 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467177 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467178 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term226 _89991 _90000 x f x' x'') = (term221 _89991 _90000 x f x' x'').
Proof. exact (MK_COMB (@lem3467177) (@lem3467176 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467179 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term226 _89991 _90000 x f x' x'') = (term222 _89991 _90000 x f x' x'').
Proof. exact (TRANS (@lem3467178 _89991 _90000 x f x' x'') (@lem3467170 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467180 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term227 _89991 _90000 x f x') = (term228 _89991 _90000 x f x').
Proof. exact (fun_ext (fun x'' : _89991 => @lem3467179 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467181 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3467182 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term224 _89991 _90000 x f x') = (term229 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3467181 _89991) (@lem3467180 _89991 _90000 x f x')). Qed.
Lemma lem3467183 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term223 _89991 _90000 x f x') = (term229 _89991 _90000 x f x').
Proof. exact (TRANS (@lem3467175 _89991 _90000 x f x') (@lem3467182 _89991 _90000 x f x')). Qed.
Lemma lem3467184 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term125 _89991 _90000 x f x') = (term125 _89991 _90000 x f x').
Proof. exact (fun_ext (fun x'' : _89991 => @lem3467173 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467185 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467186 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term126 _89991 _90000 x f x') = (term126 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3467185 _89991) (@lem3467184 _89991 _90000 x f x')). Qed.
Lemma lem3467188 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term57 _89991 s x) = (term57 _89991 s x).
Proof. exact (eq_refl (term57 _89991 s x)). Qed.
Lemma lem3467189 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term230 _89991 _90000 s x f x') = (term231 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467188 _89991 s x') (@lem3467183 _89991 _90000 x f x')). Qed.
Lemma lem3467190 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term232 _89991 _90000 s x f x') = (term230 _89991 _90000 s x f x').
Proof. exact (@lem17362 (s x') (term126 _89991 _90000 x f x')). Qed.
Lemma lem3467191 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term232 _89991 _90000 s x f x') = (term231 _89991 _90000 s x f x').
Proof. exact (TRANS (@lem3467190 _89991 _90000 s x f x') (@lem3467189 _89991 _90000 s x f x')). Qed.
Lemma lem3467193 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term233 _89991 s x) = (term233 _89991 s x).
Proof. exact (eq_refl (term233 _89991 s x)). Qed.
Lemma lem3467194 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term234 _89991 _90000 s x f x') = (term234 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467193 _89991 s x') (@lem3467186 _89991 _90000 x f x')). Qed.
Lemma lem3467195 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term128 _89991 _90000 s x f x') = (term234 _89991 _90000 s x f x').
Proof. exact (@lem17265 (s x') (term126 _89991 _90000 x f x')). Qed.
Lemma lem3467196 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term128 _89991 _90000 s x f x') = (term234 _89991 _90000 s x f x').
Proof. exact (TRANS (@lem3467195 _89991 _90000 s x f x') (@lem3467194 _89991 _90000 s x f x')). Qed.
Lemma lem3467197 {_89991 : Type'} (P : type686 _89991) : (term151 _89991 P) = (term152 _89991 P).
Proof. exact (@lem18392 (_89991 -> Prop) P). Qed.
Lemma lem3467198 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term235 _89991 _90000 s x f) = (term236 _89991 _90000 s x f).
Proof. exact (@lem3467197 _89991 (term130 _89991 _90000 s x f)). Qed.
Lemma lem3467199 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term237 _89991 _90000 s x f x') = (term128 _89991 _90000 s x f x').
Proof. exact (eq_refl (term237 _89991 _90000 s x f x')). Qed.
Lemma lem3467200 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467201 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term238 _89991 _90000 s x f x') = (term232 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467200) (@lem3467199 _89991 _90000 s x f x')). Qed.
Lemma lem3467202 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term238 _89991 _90000 s x f x') = (term231 _89991 _90000 s x f x').
Proof. exact (TRANS (@lem3467201 _89991 _90000 s x f x') (@lem3467191 _89991 _90000 s x f x')). Qed.
Lemma lem3467203 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term239 _89991 _90000 s x f) = (term240 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3467202 _89991 _90000 s x f x')). Qed.
Lemma lem3467204 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467205 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term236 _89991 _90000 s x f) = (term241 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467204 _89991) (@lem3467203 _89991 _90000 s x f)). Qed.
Lemma lem3467206 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term235 _89991 _90000 s x f) = (term241 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467198 _89991 _90000 s x f) (@lem3467205 _89991 _90000 s x f)). Qed.
Lemma lem3467207 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term130 _89991 _90000 s x f) = (term242 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3467196 _89991 _90000 s x f x')). Qed.
Lemma lem3467208 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3467209 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term131 _89991 _90000 s x f) = (term243 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467208 _89991) (@lem3467207 _89991 _90000 s x f)). Qed.
Lemma lem3467210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467211 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term244 _89991 _90000 x f s) = (term245 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467210) (@lem3467156 _89991 _90000 x f s)). Qed.
Lemma lem3467212 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term246 _89991 _90000 s x f) = (term247 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467211 _89991 _90000 x f s) (@lem3467209 _89991 _90000 s x f)). Qed.
Lemma lem3467213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467214 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term248 _89991 _90000 x f s) = (term249 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467213) (@lem3467159 _89991 _90000 x f s)). Qed.
Lemma lem3467215 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term250 _89991 _90000 s x f) = (term251 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467214 _89991 _90000 x f s) (@lem3467206 _89991 _90000 s x f)). Qed.
Lemma lem3467216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467217 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term252 _89991 _90000 s x f) = (term253 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467216) (@lem3467215 _89991 _90000 s x f)). Qed.
Lemma lem3467218 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term254 _89991 _90000 s x f) = (term255 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467217 _89991 _90000 s x f) (@lem3467212 _89991 _90000 s x f)). Qed.
Lemma lem3467219 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term149 _89991 _90000 s x f) = (term254 _89991 _90000 s x f).
Proof. exact (@lem17646 (term100 _89991 _90000 x f s) (term131 _89991 _90000 s x f)). Qed.
Lemma lem3467220 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term149 _89991 _90000 s x f) = (term255 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467219 _89991 _90000 s x f) (@lem3467218 _89991 _90000 s x f)). Qed.
Lemma lem3467551 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3467552 {_89991 : Type'} (P : _89991 -> Prop) (Q : Prop) : (term188 _89991 P Q) = (term189 _89991 P Q).
Proof. exact (@lem3467551 _89991 P Q). Qed.
Lemma lem3467553 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term256 _89991 _90000 s x f) = (term257 _89991 _90000 s x f).
Proof. exact (@lem3467552 _89991 (term219 _89991 _90000 x f s) (term241 _89991 _90000 s x f)). Qed.
Lemma lem3467554 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term258 _89991 _90000 x f s x') = (term209 _89991 _90000 x f s x').
Proof. exact (eq_refl (term258 _89991 _90000 x f s x')). Qed.
Lemma lem3467555 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term259 _89991 _90000 x f s) = (term219 _89991 _90000 x f s).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467554 _89991 _90000 x f s x')). Qed.
Lemma lem3467556 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467557 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term260 _89991 _90000 x f s) = (term220 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467556 _89991) (@lem3467555 _89991 _90000 x f s)). Qed.
Lemma lem3467558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467559 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term261 _89991 _90000 x f s) = (term249 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467558) (@lem3467557 _89991 _90000 x f s)). Qed.
Lemma lem3467560 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term241 _89991 _90000 s x f) = (term241 _89991 _90000 s x f).
Proof. exact (eq_refl (term241 _89991 _90000 s x f)). Qed.
Lemma lem3467561 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term256 _89991 _90000 s x f) = (term251 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467559 _89991 _90000 x f s) (@lem3467560 _89991 _90000 s x f)). Qed.
Lemma lem3467562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467563 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term262 _89991 _90000 s x f) = (term263 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467562) (@lem3467561 _89991 _90000 s x f)). Qed.
Lemma lem3467564 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term258 _89991 _90000 x f s x') = (term209 _89991 _90000 x f s x').
Proof. exact (eq_refl (term258 _89991 _90000 x f s x')). Qed.
Lemma lem3467565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467566 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term264 _89991 _90000 x f s x') = (term265 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467565) (@lem3467564 _89991 _90000 x f s x')). Qed.
Lemma lem3467567 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term241 _89991 _90000 s x f) = (term241 _89991 _90000 s x f).
Proof. exact (eq_refl (term241 _89991 _90000 s x f)). Qed.
Lemma lem3467568 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term266 _89991 _90000 x s x' f) = (term267 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467566 _89991 _90000 x' f s x) (@lem3467567 _89991 _90000 s x' f)). Qed.
Lemma lem3467569 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term268 _89991 _90000 s x f) = (term269 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467568 _89991 _90000 x' s x f)). Qed.
Lemma lem3467570 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467571 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term257 _89991 _90000 s x f) = (term270 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467570 _89991) (@lem3467569 _89991 _90000 s x f)). Qed.
Lemma lem3467572 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term256 _89991 _90000 s x f) = (term257 _89991 _90000 s x f)) = ((term251 _89991 _90000 s x f) = (term270 _89991 _90000 s x f)).
Proof. exact (MK_COMB (@lem3467563 _89991 _90000 s x f) (@lem3467571 _89991 _90000 s x f)). Qed.
Lemma lem3467573 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term251 _89991 _90000 s x f) = (term270 _89991 _90000 s x f).
Proof. exact (EQ_MP (@lem3467572 _89991 _90000 s x f) (@lem3467553 _89991 _90000 s x f)). Qed.
Lemma lem3467575 {A : Type'} (P : Prop) (Q : A -> Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3467576 {_89991 : Type'} (P : Prop) (Q : type686 _89991) : (term273 _89991 P Q) = (term274 _89991 P Q).
Proof. exact (@lem3467575 (_89991 -> Prop) P Q). Qed.
Lemma lem3467577 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term275 _89991 _90000 x s x' f) = (term276 _89991 _90000 x s x' f).
Proof. exact (@lem3467576 _89991 (term209 _89991 _90000 x' f s x) (term240 _89991 _90000 s x' f)). Qed.
Lemma lem3467578 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term277 _89991 _90000 s x f x') = (term231 _89991 _90000 s x f x').
Proof. exact (eq_refl (term277 _89991 _90000 s x f x')). Qed.
Lemma lem3467579 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term278 _89991 _90000 s x f) = (term240 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3467578 _89991 _90000 s x f x')). Qed.
Lemma lem3467580 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467581 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term279 _89991 _90000 s x f) = (term241 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467580 _89991) (@lem3467579 _89991 _90000 s x f)). Qed.
Lemma lem3467582 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term265 _89991 _90000 x f s x') = (term265 _89991 _90000 x f s x').
Proof. exact (eq_refl (term265 _89991 _90000 x f s x')). Qed.
Lemma lem3467583 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term275 _89991 _90000 x s x' f) = (term267 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467582 _89991 _90000 x' f s x) (@lem3467581 _89991 _90000 s x' f)). Qed.
Lemma lem3467584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467585 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term280 _89991 _90000 x s x' f) = (term281 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467584) (@lem3467583 _89991 _90000 x s x' f)). Qed.
Lemma lem3467586 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term277 _89991 _90000 s x f x') = (term231 _89991 _90000 s x f x').
Proof. exact (eq_refl (term277 _89991 _90000 s x f x')). Qed.
Lemma lem3467587 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term265 _89991 _90000 x f s x') = (term265 _89991 _90000 x f s x').
Proof. exact (eq_refl (term265 _89991 _90000 x f s x')). Qed.
Lemma lem3467588 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term282 _89991 _90000 x s x' f x'') = (term283 _89991 _90000 x s x' f x'').
Proof. exact (MK_COMB (@lem3467587 _89991 _90000 x' f s x) (@lem3467586 _89991 _90000 s x' f x'')). Qed.
Lemma lem3467589 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term284 _89991 _90000 x s x' f) = (term285 _89991 _90000 x s x' f).
Proof. exact (fun_ext (fun x'' : _89991 -> Prop => @lem3467588 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467590 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467591 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term276 _89991 _90000 x s x' f) = (term286 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467590 _89991) (@lem3467589 _89991 _90000 x s x' f)). Qed.
Lemma lem3467592 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : ((term275 _89991 _90000 x s x' f) = (term276 _89991 _90000 x s x' f)) = ((term267 _89991 _90000 x s x' f) = (term286 _89991 _90000 x s x' f)).
Proof. exact (MK_COMB (@lem3467585 _89991 _90000 x s x' f) (@lem3467591 _89991 _90000 x s x' f)). Qed.
Lemma lem3467593 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term267 _89991 _90000 x s x' f) = (term286 _89991 _90000 x s x' f).
Proof. exact (EQ_MP (@lem3467592 _89991 _90000 x s x' f) (@lem3467577 _89991 _90000 x s x' f)). Qed.
Lemma lem3467594 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term269 _89991 _90000 s x f) = (term287 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467593 _89991 _90000 x' s x f)). Qed.
Lemma lem3467595 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467596 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term270 _89991 _90000 s x f) = (term288 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467595 _89991) (@lem3467594 _89991 _90000 s x f)). Qed.
Lemma lem3467597 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term251 _89991 _90000 s x f) = (term288 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467573 _89991 _90000 s x f) (@lem3467596 _89991 _90000 s x f)). Qed.
Lemma lem3467598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467599 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term253 _89991 _90000 s x f) = (term289 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467598) (@lem3467597 _89991 _90000 s x f)). Qed.
Lemma lem3467601 {A : Type'} (P : Prop) (Q : A -> Prop) : (term290 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3467602 {_89991 : Type'} (P : Prop) (Q : type686 _89991) : (term292 _89991 P Q) = (term293 _89991 P Q).
Proof. exact (@lem3467601 (_89991 -> Prop) P Q). Qed.
Lemma lem3467603 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term294 _89991 _90000 x f s x') = (term295 _89991 _90000 x f s x').
Proof. exact (@lem3467602 _89991 (term296 _89991 _90000 x f x') (term201 _89991 s x')). Qed.
Lemma lem3467604 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term297 _89991 s x t) = (term194 _89991 s t x).
Proof. exact (eq_refl (term297 _89991 s x t)). Qed.
Lemma lem3467605 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term298 _89991 s x) = (term201 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3467604 _89991 s t x)). Qed.
Lemma lem3467606 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467607 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term299 _89991 s x) = (term202 _89991 s x).
Proof. exact (MK_COMB (@lem3467606 _89991) (@lem3467605 _89991 s x)). Qed.
Lemma lem3467608 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term205 _89991 _90000 x f x') = (term205 _89991 _90000 x f x').
Proof. exact (eq_refl (term205 _89991 _90000 x f x')). Qed.
Lemma lem3467609 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term294 _89991 _90000 x f s x') = (term207 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467608 _89991 _90000 x f x') (@lem3467607 _89991 s x')). Qed.
Lemma lem3467610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467611 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term300 _89991 _90000 x f s x') = (term301 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467610) (@lem3467609 _89991 _90000 x f s x')). Qed.
Lemma lem3467612 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term297 _89991 s x t) = (term194 _89991 s t x).
Proof. exact (eq_refl (term297 _89991 s x t)). Qed.
Lemma lem3467613 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term205 _89991 _90000 x f x') = (term205 _89991 _90000 x f x').
Proof. exact (eq_refl (term205 _89991 _90000 x f x')). Qed.
Lemma lem3467614 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : _89991 -> Prop) (x' : _89991) : (term302 _89991 _90000 x f s x' t) = (term303 _89991 _90000 x f s t x').
Proof. exact (MK_COMB (@lem3467613 _89991 _90000 x f x') (@lem3467612 _89991 s t x')). Qed.
Lemma lem3467615 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term304 _89991 _90000 x f s x') = (term305 _89991 _90000 x f s x').
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3467614 _89991 _90000 x f s t x')). Qed.
Lemma lem3467616 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467617 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term295 _89991 _90000 x f s x') = (term306 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467616 _89991) (@lem3467615 _89991 _90000 x f s x')). Qed.
Lemma lem3467618 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : ((term294 _89991 _90000 x f s x') = (term295 _89991 _90000 x f s x')) = ((term207 _89991 _90000 x f s x') = (term306 _89991 _90000 x f s x')).
Proof. exact (MK_COMB (@lem3467611 _89991 _90000 x f s x') (@lem3467617 _89991 _90000 x f s x')). Qed.
Lemma lem3467619 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term207 _89991 _90000 x f s x') = (term306 _89991 _90000 x f s x').
Proof. exact (EQ_MP (@lem3467618 _89991 _90000 x f s x') (@lem3467603 _89991 _90000 x f s x')). Qed.
Lemma lem3467620 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term217 _89991 _90000 x f s) = (term307 _89991 _90000 x f s).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467619 _89991 _90000 x f s x')). Qed.
Lemma lem3467621 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3467622 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term218 _89991 _90000 x f s) = (term308 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467621 _89991) (@lem3467620 _89991 _90000 x f s)). Qed.
Lemma lem3467624 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3467625 {_89991 : Type'} (P : type1364 _89991) : (term311 _89991 P) = (term312 _89991 P).
Proof. exact (@lem3467624 _89991 (_89991 -> Prop) P). Qed.
Lemma lem3467626 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term313 _89991 _90000 x f s) = (term314 _89991 _90000 x f s).
Proof. exact (@lem3467625 _89991 (term315 _89991 _90000 x f s)). Qed.
Lemma lem3467627 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term316 _89991 _90000 x f s x') = (term305 _89991 _90000 x f s x').
Proof. exact (eq_refl (term316 _89991 _90000 x f s x')). Qed.
Lemma lem3467628 {_89991 : Type'} (t : _89991 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3467629 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) (t : _89991 -> Prop) : (term317 _89991 _90000 x f s x' t) = (term318 _89991 _90000 x f s x' t).
Proof. exact (MK_COMB (@lem3467627 _89991 _90000 x f s x') (@lem3467628 _89991 t)). Qed.
Lemma lem3467630 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : _89991 -> Prop) (x' : _89991) : (term318 _89991 _90000 x f s x' t) = (term303 _89991 _90000 x f s t x').
Proof. exact (eq_refl (term318 _89991 _90000 x f s x' t)). Qed.
Lemma lem3467631 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : _89991 -> Prop) (x' : _89991) : (term317 _89991 _90000 x f s x' t) = (term303 _89991 _90000 x f s t x').
Proof. exact (TRANS (@lem3467629 _89991 _90000 x f s x' t) (@lem3467630 _89991 _90000 x f s t x')). Qed.
Lemma lem3467632 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term319 _89991 _90000 x f s x') = (term305 _89991 _90000 x f s x').
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3467631 _89991 _90000 x f s t x')). Qed.
Lemma lem3467633 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467634 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term320 _89991 _90000 x f s x') = (term306 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3467633 _89991) (@lem3467632 _89991 _90000 x f s x')). Qed.
Lemma lem3467635 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term321 _89991 _90000 x f s) = (term307 _89991 _90000 x f s).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467634 _89991 _90000 x f s x')). Qed.
Lemma lem3467636 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3467637 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term313 _89991 _90000 x f s) = (term308 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467636 _89991) (@lem3467635 _89991 _90000 x f s)). Qed.
Lemma lem3467638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467639 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term322 _89991 _90000 x f s) = (term323 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467638) (@lem3467637 _89991 _90000 x f s)). Qed.
Lemma lem3467640 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term316 _89991 _90000 x f s x') = (term305 _89991 _90000 x f s x').
Proof. exact (eq_refl (term316 _89991 _90000 x f s x')). Qed.
Lemma lem3467641 {_89991 : Type'} (t : type1402 _89991) (x : _89991) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3467642 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) (x' : _89991) : (term324 _89991 _90000 x f s t x') = (term325 _89991 _90000 x f s t x').
Proof. exact (MK_COMB (@lem3467640 _89991 _90000 x f s x') (@lem3467641 _89991 t x')). Qed.
Lemma lem3467643 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) (x' : _89991) : (term325 _89991 _90000 x f s t x') = (term326 _89991 _90000 x f s t x').
Proof. exact (eq_refl (term325 _89991 _90000 x f s t x')). Qed.
Lemma lem3467644 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) (x' : _89991) : (term324 _89991 _90000 x f s t x') = (term326 _89991 _90000 x f s t x').
Proof. exact (TRANS (@lem3467642 _89991 _90000 x f s t x') (@lem3467643 _89991 _90000 x f s t x')). Qed.
Lemma lem3467645 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term327 _89991 _90000 x f s t) = (term328 _89991 _90000 x f s t).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467644 _89991 _90000 x f s t x')). Qed.
Lemma lem3467646 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3467647 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term329 _89991 _90000 x f s t) = (term330 _89991 _90000 x f s t).
Proof. exact (MK_COMB (@lem3467646 _89991) (@lem3467645 _89991 _90000 x f s t)). Qed.
Lemma lem3467648 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term331 _89991 _90000 x f s) = (term332 _89991 _90000 x f s).
Proof. exact (fun_ext (fun t : type1402 _89991 => @lem3467647 _89991 _90000 x f s t)). Qed.
Lemma lem3467649 {_89991 : Type'} : (@ex (_89991 -> _89991 -> Prop)) = (@ex (_89991 -> _89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> _89991 -> Prop))). Qed.
Lemma lem3467650 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term314 _89991 _90000 x f s) = (term333 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467649 _89991) (@lem3467648 _89991 _90000 x f s)). Qed.
Lemma lem3467651 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : ((term313 _89991 _90000 x f s) = (term314 _89991 _90000 x f s)) = ((term308 _89991 _90000 x f s) = (term333 _89991 _90000 x f s)).
Proof. exact (MK_COMB (@lem3467639 _89991 _90000 x f s) (@lem3467650 _89991 _90000 x f s)). Qed.
Lemma lem3467652 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term308 _89991 _90000 x f s) = (term333 _89991 _90000 x f s).
Proof. exact (EQ_MP (@lem3467651 _89991 _90000 x f s) (@lem3467626 _89991 _90000 x f s)). Qed.
Lemma lem3467653 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term218 _89991 _90000 x f s) = (term333 _89991 _90000 x f s).
Proof. exact (TRANS (@lem3467622 _89991 _90000 x f s) (@lem3467652 _89991 _90000 x f s)). Qed.
Lemma lem3467654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467655 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term245 _89991 _90000 x f s) = (term334 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467654) (@lem3467653 _89991 _90000 x f s)). Qed.
Lemma lem3467657 {A : Type'} (P : Prop) (Q : A -> Prop) : (term290 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3467658 {_89991 : Type'} (P : Prop) (Q : _89991 -> Prop) : (term290 _89991 P Q) = (term291 _89991 P Q).
Proof. exact (@lem3467657 _89991 P Q). Qed.
Lemma lem3467659 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term335 _89991 _90000 s x f x') = (term336 _89991 _90000 s x f x').
Proof. exact (@lem3467658 _89991 (term48 _89991 s x') (term125 _89991 _90000 x f x')). Qed.
Lemma lem3467660 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term225 _89991 _90000 x f x' x'') = (term123 _89991 _90000 x f x' x'').
Proof. exact (eq_refl (term225 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467661 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term337 _89991 _90000 x f x') = (term125 _89991 _90000 x f x').
Proof. exact (fun_ext (fun x'' : _89991 => @lem3467660 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467662 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467663 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term338 _89991 _90000 x f x') = (term126 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3467662 _89991) (@lem3467661 _89991 _90000 x f x')). Qed.
Lemma lem3467664 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term233 _89991 s x) = (term233 _89991 s x).
Proof. exact (eq_refl (term233 _89991 s x)). Qed.
Lemma lem3467665 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term335 _89991 _90000 s x f x') = (term234 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467664 _89991 s x') (@lem3467663 _89991 _90000 x f x')). Qed.
Lemma lem3467666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467667 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term339 _89991 _90000 s x f x') = (term340 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467666) (@lem3467665 _89991 _90000 s x f x')). Qed.
Lemma lem3467668 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term225 _89991 _90000 x f x' x'') = (term123 _89991 _90000 x f x' x'').
Proof. exact (eq_refl (term225 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467669 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term233 _89991 s x) = (term233 _89991 s x).
Proof. exact (eq_refl (term233 _89991 s x)). Qed.
Lemma lem3467670 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term341 _89991 _90000 s x f x' x'') = (term342 _89991 _90000 s x f x' x'').
Proof. exact (MK_COMB (@lem3467669 _89991 s x') (@lem3467668 _89991 _90000 x f x' x'')). Qed.
Lemma lem3467671 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term343 _89991 _90000 s x f x') = (term344 _89991 _90000 s x f x').
Proof. exact (fun_ext (fun x'' : _89991 => @lem3467670 _89991 _90000 s x f x' x'')). Qed.
Lemma lem3467672 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467673 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term336 _89991 _90000 s x f x') = (term345 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467672 _89991) (@lem3467671 _89991 _90000 s x f x')). Qed.
Lemma lem3467674 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : ((term335 _89991 _90000 s x f x') = (term336 _89991 _90000 s x f x')) = ((term234 _89991 _90000 s x f x') = (term345 _89991 _90000 s x f x')).
Proof. exact (MK_COMB (@lem3467667 _89991 _90000 s x f x') (@lem3467673 _89991 _90000 s x f x')). Qed.
Lemma lem3467675 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term234 _89991 _90000 s x f x') = (term345 _89991 _90000 s x f x').
Proof. exact (EQ_MP (@lem3467674 _89991 _90000 s x f x') (@lem3467659 _89991 _90000 s x f x')). Qed.
Lemma lem3467676 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term242 _89991 _90000 s x f) = (term346 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3467675 _89991 _90000 s x f x')). Qed.
Lemma lem3467677 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3467678 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term243 _89991 _90000 s x f) = (term347 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467677 _89991) (@lem3467676 _89991 _90000 s x f)). Qed.
Lemma lem3467680 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3467681 {_89991 : Type'} (P : type672 _89991) : (term348 _89991 P) = (term349 _89991 P).
Proof. exact (@lem3467680 (_89991 -> Prop) _89991 P). Qed.
Lemma lem3467682 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term350 _89991 _90000 s x f) = (term351 _89991 _90000 s x f).
Proof. exact (@lem3467681 _89991 (term352 _89991 _90000 s x f)). Qed.
Lemma lem3467683 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term353 _89991 _90000 s x f x') = (term344 _89991 _90000 s x f x').
Proof. exact (eq_refl (term353 _89991 _90000 s x f x')). Qed.
Lemma lem3467684 {_89991 : Type'} (x : _89991) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3467685 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term354 _89991 _90000 s x f x' x'') = (term355 _89991 _90000 s x f x' x'').
Proof. exact (MK_COMB (@lem3467683 _89991 _90000 s x f x') (@lem3467684 _89991 x'')). Qed.
Lemma lem3467686 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term355 _89991 _90000 s x f x' x'') = (term342 _89991 _90000 s x f x' x'').
Proof. exact (eq_refl (term355 _89991 _90000 s x f x' x'')). Qed.
Lemma lem3467687 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) (x'' : _89991) : (term354 _89991 _90000 s x f x' x'') = (term342 _89991 _90000 s x f x' x'').
Proof. exact (TRANS (@lem3467685 _89991 _90000 s x f x' x'') (@lem3467686 _89991 _90000 s x f x' x'')). Qed.
Lemma lem3467688 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term356 _89991 _90000 s x f x') = (term344 _89991 _90000 s x f x').
Proof. exact (fun_ext (fun x'' : _89991 => @lem3467687 _89991 _90000 s x f x' x'')). Qed.
Lemma lem3467689 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467690 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term357 _89991 _90000 s x f x') = (term345 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467689 _89991) (@lem3467688 _89991 _90000 s x f x')). Qed.
Lemma lem3467691 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term358 _89991 _90000 s x f) = (term346 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3467690 _89991 _90000 s x f x')). Qed.
Lemma lem3467692 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3467693 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term350 _89991 _90000 s x f) = (term347 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467692 _89991) (@lem3467691 _89991 _90000 s x f)). Qed.
Lemma lem3467694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467695 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term359 _89991 _90000 s x f) = (term360 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467694) (@lem3467693 _89991 _90000 s x f)). Qed.
Lemma lem3467696 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : _89991 -> Prop) : (term353 _89991 _90000 s x f x') = (term344 _89991 _90000 s x f x').
Proof. exact (eq_refl (term353 _89991 _90000 s x f x')). Qed.
Lemma lem3467697 {_89991 : Type'} (x : type684 _89991) (x' : _89991 -> Prop) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem3467698 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) (x'' : _89991 -> Prop) : (term361 _89991 _90000 s x f x' x'') = (term362 _89991 _90000 s x f x' x'').
Proof. exact (MK_COMB (@lem3467696 _89991 _90000 s x f x'') (@lem3467697 _89991 x' x'')). Qed.
Lemma lem3467699 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) (x'' : _89991 -> Prop) : (term362 _89991 _90000 s x f x' x'') = (term363 _89991 _90000 s x f x' x'').
Proof. exact (eq_refl (term362 _89991 _90000 s x f x' x'')). Qed.
Lemma lem3467700 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) (x'' : _89991 -> Prop) : (term361 _89991 _90000 s x f x' x'') = (term363 _89991 _90000 s x f x' x'').
Proof. exact (TRANS (@lem3467698 _89991 _90000 s x f x' x'') (@lem3467699 _89991 _90000 s x f x' x'')). Qed.
Lemma lem3467701 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) : (term364 _89991 _90000 s x f x') = (term365 _89991 _90000 s x f x').
Proof. exact (fun_ext (fun x'' : _89991 -> Prop => @lem3467700 _89991 _90000 s x f x' x'')). Qed.
Lemma lem3467702 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3467703 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) : (term366 _89991 _90000 s x f x') = (term367 _89991 _90000 s x f x').
Proof. exact (MK_COMB (@lem3467702 _89991) (@lem3467701 _89991 _90000 s x f x')). Qed.
Lemma lem3467704 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term368 _89991 _90000 s x f) = (term369 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : type684 _89991 => @lem3467703 _89991 _90000 s x f x')). Qed.
Lemma lem3467705 {_89991 : Type'} : (@ex ((_89991 -> Prop) -> _89991)) = (@ex ((_89991 -> Prop) -> _89991)).
Proof. exact (eq_refl (@ex ((_89991 -> Prop) -> _89991))). Qed.
Lemma lem3467706 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term351 _89991 _90000 s x f) = (term370 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467705 _89991) (@lem3467704 _89991 _90000 s x f)). Qed.
Lemma lem3467707 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term350 _89991 _90000 s x f) = (term351 _89991 _90000 s x f)) = ((term347 _89991 _90000 s x f) = (term370 _89991 _90000 s x f)).
Proof. exact (MK_COMB (@lem3467695 _89991 _90000 s x f) (@lem3467706 _89991 _90000 s x f)). Qed.
Lemma lem3467708 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term347 _89991 _90000 s x f) = (term370 _89991 _90000 s x f).
Proof. exact (EQ_MP (@lem3467707 _89991 _90000 s x f) (@lem3467682 _89991 _90000 s x f)). Qed.
Lemma lem3467709 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term243 _89991 _90000 s x f) = (term370 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467678 _89991 _90000 s x f) (@lem3467708 _89991 _90000 s x f)). Qed.
Lemma lem3467710 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term247 _89991 _90000 s x f) = (term371 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467655 _89991 _90000 x f s) (@lem3467709 _89991 _90000 s x f)). Qed.
Lemma lem3467712 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3467713 {_89991 : Type'} (P : type421 _89991) (Q : Prop) : (term372 _89991 P Q) = (term373 _89991 P Q).
Proof. exact (@lem3467712 (type1402 _89991) P Q). Qed.
Lemma lem3467714 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term374 _89991 _90000 s x f) = (term375 _89991 _90000 s x f).
Proof. exact (@lem3467713 _89991 (term332 _89991 _90000 x f s) (term370 _89991 _90000 s x f)). Qed.
Lemma lem3467715 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term376 _89991 _90000 x f s t) = (term330 _89991 _90000 x f s t).
Proof. exact (eq_refl (term376 _89991 _90000 x f s t)). Qed.
Lemma lem3467716 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term377 _89991 _90000 x f s) = (term332 _89991 _90000 x f s).
Proof. exact (fun_ext (fun t : type1402 _89991 => @lem3467715 _89991 _90000 x f s t)). Qed.
Lemma lem3467717 {_89991 : Type'} : (@ex (_89991 -> _89991 -> Prop)) = (@ex (_89991 -> _89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> _89991 -> Prop))). Qed.
Lemma lem3467718 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term378 _89991 _90000 x f s) = (term333 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467717 _89991) (@lem3467716 _89991 _90000 x f s)). Qed.
Lemma lem3467719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467720 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) : (term379 _89991 _90000 x f s) = (term334 _89991 _90000 x f s).
Proof. exact (MK_COMB (@lem3467719) (@lem3467718 _89991 _90000 x f s)). Qed.
Lemma lem3467721 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term370 _89991 _90000 s x f) = (term370 _89991 _90000 s x f).
Proof. exact (eq_refl (term370 _89991 _90000 s x f)). Qed.
Lemma lem3467722 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term374 _89991 _90000 s x f) = (term371 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467720 _89991 _90000 x f s) (@lem3467721 _89991 _90000 s x f)). Qed.
Lemma lem3467723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467724 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term380 _89991 _90000 s x f) = (term381 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467723) (@lem3467722 _89991 _90000 s x f)). Qed.
Lemma lem3467725 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term376 _89991 _90000 x f s t) = (term330 _89991 _90000 x f s t).
Proof. exact (eq_refl (term376 _89991 _90000 x f s t)). Qed.
Lemma lem3467726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467727 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term382 _89991 _90000 x f s t) = (term383 _89991 _90000 x f s t).
Proof. exact (MK_COMB (@lem3467726) (@lem3467725 _89991 _90000 x f s t)). Qed.
Lemma lem3467728 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term370 _89991 _90000 s x f) = (term370 _89991 _90000 s x f).
Proof. exact (eq_refl (term370 _89991 _90000 s x f)). Qed.
Lemma lem3467729 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term384 _89991 _90000 t s x f) = (term385 _89991 _90000 t s x f).
Proof. exact (MK_COMB (@lem3467727 _89991 _90000 x f s t) (@lem3467728 _89991 _90000 s x f)). Qed.
Lemma lem3467730 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term386 _89991 _90000 s x f) = (term387 _89991 _90000 s x f).
Proof. exact (fun_ext (fun t : type1402 _89991 => @lem3467729 _89991 _90000 t s x f)). Qed.
Lemma lem3467731 {_89991 : Type'} : (@ex (_89991 -> _89991 -> Prop)) = (@ex (_89991 -> _89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> _89991 -> Prop))). Qed.
Lemma lem3467732 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term375 _89991 _90000 s x f) = (term388 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467731 _89991) (@lem3467730 _89991 _90000 s x f)). Qed.
Lemma lem3467733 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term374 _89991 _90000 s x f) = (term375 _89991 _90000 s x f)) = ((term371 _89991 _90000 s x f) = (term388 _89991 _90000 s x f)).
Proof. exact (MK_COMB (@lem3467724 _89991 _90000 s x f) (@lem3467732 _89991 _90000 s x f)). Qed.
Lemma lem3467734 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term371 _89991 _90000 s x f) = (term388 _89991 _90000 s x f).
Proof. exact (EQ_MP (@lem3467733 _89991 _90000 s x f) (@lem3467714 _89991 _90000 s x f)). Qed.
Lemma lem3467736 {A : Type'} (P : Prop) (Q : A -> Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3467737 {_89991 : Type'} (P : Prop) (Q : type162 _89991) : (term389 _89991 P Q) = (term390 _89991 P Q).
Proof. exact (@lem3467736 (type684 _89991) P Q). Qed.
Lemma lem3467738 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term391 _89991 _90000 t s x f) = (term392 _89991 _90000 t s x f).
Proof. exact (@lem3467737 _89991 (term330 _89991 _90000 x f s t) (term369 _89991 _90000 s x f)). Qed.
Lemma lem3467739 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) : (term393 _89991 _90000 s x f x') = (term367 _89991 _90000 s x f x').
Proof. exact (eq_refl (term393 _89991 _90000 s x f x')). Qed.
Lemma lem3467740 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term394 _89991 _90000 s x f) = (term369 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : type684 _89991 => @lem3467739 _89991 _90000 s x f x')). Qed.
Lemma lem3467741 {_89991 : Type'} : (@ex ((_89991 -> Prop) -> _89991)) = (@ex ((_89991 -> Prop) -> _89991)).
Proof. exact (eq_refl (@ex ((_89991 -> Prop) -> _89991))). Qed.
Lemma lem3467742 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term395 _89991 _90000 s x f) = (term370 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467741 _89991) (@lem3467740 _89991 _90000 s x f)). Qed.
Lemma lem3467743 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term383 _89991 _90000 x f s t) = (term383 _89991 _90000 x f s t).
Proof. exact (eq_refl (term383 _89991 _90000 x f s t)). Qed.
Lemma lem3467744 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term391 _89991 _90000 t s x f) = (term385 _89991 _90000 t s x f).
Proof. exact (MK_COMB (@lem3467743 _89991 _90000 x f s t) (@lem3467742 _89991 _90000 s x f)). Qed.
Lemma lem3467745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467746 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term396 _89991 _90000 t s x f) = (term397 _89991 _90000 t s x f).
Proof. exact (MK_COMB (@lem3467745) (@lem3467744 _89991 _90000 t s x f)). Qed.
Lemma lem3467747 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) : (term393 _89991 _90000 s x f x') = (term367 _89991 _90000 s x f x').
Proof. exact (eq_refl (term393 _89991 _90000 s x f x')). Qed.
Lemma lem3467748 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term383 _89991 _90000 x f s t) = (term383 _89991 _90000 x f s t).
Proof. exact (eq_refl (term383 _89991 _90000 x f s t)). Qed.
Lemma lem3467749 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) : (term398 _89991 _90000 t s x f x') = (term399 _89991 _90000 t s x f x').
Proof. exact (MK_COMB (@lem3467748 _89991 _90000 x f s t) (@lem3467747 _89991 _90000 s x f x')). Qed.
Lemma lem3467750 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term400 _89991 _90000 t s x f) = (term401 _89991 _90000 t s x f).
Proof. exact (fun_ext (fun x' : type684 _89991 => @lem3467749 _89991 _90000 t s x f x')). Qed.
Lemma lem3467751 {_89991 : Type'} : (@ex ((_89991 -> Prop) -> _89991)) = (@ex ((_89991 -> Prop) -> _89991)).
Proof. exact (eq_refl (@ex ((_89991 -> Prop) -> _89991))). Qed.
Lemma lem3467752 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term392 _89991 _90000 t s x f) = (term402 _89991 _90000 t s x f).
Proof. exact (MK_COMB (@lem3467751 _89991) (@lem3467750 _89991 _90000 t s x f)). Qed.
Lemma lem3467753 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term391 _89991 _90000 t s x f) = (term392 _89991 _90000 t s x f)) = ((term385 _89991 _90000 t s x f) = (term402 _89991 _90000 t s x f)).
Proof. exact (MK_COMB (@lem3467746 _89991 _90000 t s x f) (@lem3467752 _89991 _90000 t s x f)). Qed.
Lemma lem3467754 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term385 _89991 _90000 t s x f) = (term402 _89991 _90000 t s x f).
Proof. exact (EQ_MP (@lem3467753 _89991 _90000 t s x f) (@lem3467738 _89991 _90000 t s x f)). Qed.
Lemma lem3467755 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term387 _89991 _90000 s x f) = (term403 _89991 _90000 s x f).
Proof. exact (fun_ext (fun t : type1402 _89991 => @lem3467754 _89991 _90000 t s x f)). Qed.
Lemma lem3467756 {_89991 : Type'} : (@ex (_89991 -> _89991 -> Prop)) = (@ex (_89991 -> _89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> _89991 -> Prop))). Qed.
Lemma lem3467757 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term388 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467756 _89991) (@lem3467755 _89991 _90000 s x f)). Qed.
Lemma lem3467758 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term371 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467734 _89991 _90000 s x f) (@lem3467757 _89991 _90000 s x f)). Qed.
Lemma lem3467759 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term247 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467710 _89991 _90000 s x f) (@lem3467758 _89991 _90000 s x f)). Qed.
Lemma lem3467760 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term255 _89991 _90000 s x f) = (term405 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467599 _89991 _90000 s x f) (@lem3467759 _89991 _90000 s x f)). Qed.
Lemma lem3467764 {A : Type'} (P : A -> Prop) (Q : Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3467765 {_89991 : Type'} (P : _89991 -> Prop) (Q : Prop) : (term406 _89991 P Q) = (term407 _89991 P Q).
Proof. exact (@lem3467764 _89991 P Q). Qed.
Lemma lem3467766 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term408 _89991 _90000 s x f) = (term409 _89991 _90000 s x f).
Proof. exact (@lem3467765 _89991 (term287 _89991 _90000 s x f) (term404 _89991 _90000 s x f)). Qed.
Lemma lem3467767 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term410 _89991 _90000 s x' f x) = (term286 _89991 _90000 x s x' f).
Proof. exact (eq_refl (term410 _89991 _90000 s x' f x)). Qed.
Lemma lem3467768 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term411 _89991 _90000 s x f) = (term287 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467767 _89991 _90000 x' s x f)). Qed.
Lemma lem3467769 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467770 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term412 _89991 _90000 s x f) = (term288 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467769 _89991) (@lem3467768 _89991 _90000 s x f)). Qed.
Lemma lem3467771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467772 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term413 _89991 _90000 s x f) = (term289 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467771) (@lem3467770 _89991 _90000 s x f)). Qed.
Lemma lem3467773 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term404 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (eq_refl (term404 _89991 _90000 s x f)). Qed.
Lemma lem3467774 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term408 _89991 _90000 s x f) = (term405 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467772 _89991 _90000 s x f) (@lem3467773 _89991 _90000 s x f)). Qed.
Lemma lem3467775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467776 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term414 _89991 _90000 s x f) = (term415 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467775) (@lem3467774 _89991 _90000 s x f)). Qed.
Lemma lem3467777 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term410 _89991 _90000 s x' f x) = (term286 _89991 _90000 x s x' f).
Proof. exact (eq_refl (term410 _89991 _90000 s x' f x)). Qed.
Lemma lem3467778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467779 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term416 _89991 _90000 s x' f x) = (term417 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467778) (@lem3467777 _89991 _90000 x s x' f)). Qed.
Lemma lem3467780 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term404 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (eq_refl (term404 _89991 _90000 s x f)). Qed.
Lemma lem3467781 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term418 _89991 _90000 x s x' f) = (term419 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467779 _89991 _90000 x s x' f) (@lem3467780 _89991 _90000 s x' f)). Qed.
Lemma lem3467782 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term420 _89991 _90000 s x f) = (term421 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467781 _89991 _90000 x' s x f)). Qed.
Lemma lem3467783 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467784 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term409 _89991 _90000 s x f) = (term422 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467783 _89991) (@lem3467782 _89991 _90000 s x f)). Qed.
Lemma lem3467785 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : ((term408 _89991 _90000 s x f) = (term409 _89991 _90000 s x f)) = ((term405 _89991 _90000 s x f) = (term422 _89991 _90000 s x f)).
Proof. exact (MK_COMB (@lem3467776 _89991 _90000 s x f) (@lem3467784 _89991 _90000 s x f)). Qed.
Lemma lem3467786 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term405 _89991 _90000 s x f) = (term422 _89991 _90000 s x f).
Proof. exact (EQ_MP (@lem3467785 _89991 _90000 s x f) (@lem3467766 _89991 _90000 s x f)). Qed.
Lemma lem3467790 {A : Type'} (P : A -> Prop) (Q : Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3467791 {_89991 : Type'} (P : type686 _89991) (Q : Prop) : (term423 _89991 P Q) = (term424 _89991 P Q).
Proof. exact (@lem3467790 (_89991 -> Prop) P Q). Qed.
Lemma lem3467792 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term425 _89991 _90000 x s x' f) = (term426 _89991 _90000 x s x' f).
Proof. exact (@lem3467791 _89991 (term285 _89991 _90000 x s x' f) (term404 _89991 _90000 s x' f)). Qed.
Lemma lem3467793 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term427 _89991 _90000 x s x' f x'') = (term283 _89991 _90000 x s x' f x'').
Proof. exact (eq_refl (term427 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467794 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term428 _89991 _90000 x s x' f) = (term285 _89991 _90000 x s x' f).
Proof. exact (fun_ext (fun x'' : _89991 -> Prop => @lem3467793 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467795 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467796 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term429 _89991 _90000 x s x' f) = (term286 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467795 _89991) (@lem3467794 _89991 _90000 x s x' f)). Qed.
Lemma lem3467797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467798 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term430 _89991 _90000 x s x' f) = (term417 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467797) (@lem3467796 _89991 _90000 x s x' f)). Qed.
Lemma lem3467799 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term404 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (eq_refl (term404 _89991 _90000 s x f)). Qed.
Lemma lem3467800 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term425 _89991 _90000 x s x' f) = (term419 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467798 _89991 _90000 x s x' f) (@lem3467799 _89991 _90000 s x' f)). Qed.
Lemma lem3467801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467802 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term431 _89991 _90000 x s x' f) = (term432 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467801) (@lem3467800 _89991 _90000 x s x' f)). Qed.
Lemma lem3467803 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term427 _89991 _90000 x s x' f x'') = (term283 _89991 _90000 x s x' f x'').
Proof. exact (eq_refl (term427 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467805 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term433 _89991 _90000 x s x' f x'') = (term434 _89991 _90000 x s x' f x'').
Proof. exact (MK_COMB (@lem3467804) (@lem3467803 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467806 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term404 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (eq_refl (term404 _89991 _90000 s x f)). Qed.
Lemma lem3467807 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term435 _89991 _90000 x x' s x'' f) = (term436 _89991 _90000 x x' s x'' f).
Proof. exact (MK_COMB (@lem3467805 _89991 _90000 x s x'' f x') (@lem3467806 _89991 _90000 s x'' f)). Qed.
Lemma lem3467808 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term437 _89991 _90000 x s x' f) = (term438 _89991 _90000 x s x' f).
Proof. exact (fun_ext (fun x'' : _89991 -> Prop => @lem3467807 _89991 _90000 x x'' s x' f)). Qed.
Lemma lem3467809 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467810 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term426 _89991 _90000 x s x' f) = (term439 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467809 _89991) (@lem3467808 _89991 _90000 x s x' f)). Qed.
Lemma lem3467811 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : ((term425 _89991 _90000 x s x' f) = (term426 _89991 _90000 x s x' f)) = ((term419 _89991 _90000 x s x' f) = (term439 _89991 _90000 x s x' f)).
Proof. exact (MK_COMB (@lem3467802 _89991 _90000 x s x' f) (@lem3467810 _89991 _90000 x s x' f)). Qed.
Lemma lem3467812 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term419 _89991 _90000 x s x' f) = (term439 _89991 _90000 x s x' f).
Proof. exact (EQ_MP (@lem3467811 _89991 _90000 x s x' f) (@lem3467792 _89991 _90000 x s x' f)). Qed.
Lemma lem3467814 {A : Type'} (P : Prop) (Q : A -> Prop) : (term290 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3467815 {_89991 : Type'} (P : Prop) (Q : type421 _89991) : (term440 _89991 P Q) = (term441 _89991 P Q).
Proof. exact (@lem3467814 (type1402 _89991) P Q). Qed.
Lemma lem3467816 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term442 _89991 _90000 x x' s x'' f) = (term443 _89991 _90000 x x' s x'' f).
Proof. exact (@lem3467815 _89991 (term283 _89991 _90000 x s x'' f x') (term403 _89991 _90000 s x'' f)). Qed.
Lemma lem3467817 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term444 _89991 _90000 s x f t) = (term402 _89991 _90000 t s x f).
Proof. exact (eq_refl (term444 _89991 _90000 s x f t)). Qed.
Lemma lem3467818 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term445 _89991 _90000 s x f) = (term403 _89991 _90000 s x f).
Proof. exact (fun_ext (fun t : type1402 _89991 => @lem3467817 _89991 _90000 t s x f)). Qed.
Lemma lem3467819 {_89991 : Type'} : (@ex (_89991 -> _89991 -> Prop)) = (@ex (_89991 -> _89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> _89991 -> Prop))). Qed.
Lemma lem3467820 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term446 _89991 _90000 s x f) = (term404 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467819 _89991) (@lem3467818 _89991 _90000 s x f)). Qed.
Lemma lem3467821 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term434 _89991 _90000 x s x' f x'') = (term434 _89991 _90000 x s x' f x'').
Proof. exact (eq_refl (term434 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467822 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term442 _89991 _90000 x x' s x'' f) = (term436 _89991 _90000 x x' s x'' f).
Proof. exact (MK_COMB (@lem3467821 _89991 _90000 x s x'' f x') (@lem3467820 _89991 _90000 s x'' f)). Qed.
Lemma lem3467823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467824 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term447 _89991 _90000 x x' s x'' f) = (term448 _89991 _90000 x x' s x'' f).
Proof. exact (MK_COMB (@lem3467823) (@lem3467822 _89991 _90000 x x' s x'' f)). Qed.
Lemma lem3467825 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term444 _89991 _90000 s x f t) = (term402 _89991 _90000 t s x f).
Proof. exact (eq_refl (term444 _89991 _90000 s x f t)). Qed.
Lemma lem3467826 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term434 _89991 _90000 x s x' f x'') = (term434 _89991 _90000 x s x' f x'').
Proof. exact (eq_refl (term434 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467827 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term449 _89991 _90000 x x' s x'' f t) = (term450 _89991 _90000 x x' t s x'' f).
Proof. exact (MK_COMB (@lem3467826 _89991 _90000 x s x'' f x') (@lem3467825 _89991 _90000 t s x'' f)). Qed.
Lemma lem3467828 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term451 _89991 _90000 x x' s x'' f) = (term452 _89991 _90000 x x' s x'' f).
Proof. exact (fun_ext (fun t : type1402 _89991 => @lem3467827 _89991 _90000 x x' t s x'' f)). Qed.
Lemma lem3467829 {_89991 : Type'} : (@ex (_89991 -> _89991 -> Prop)) = (@ex (_89991 -> _89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> _89991 -> Prop))). Qed.
Lemma lem3467830 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term443 _89991 _90000 x x' s x'' f) = (term453 _89991 _90000 x x' s x'' f).
Proof. exact (MK_COMB (@lem3467829 _89991) (@lem3467828 _89991 _90000 x x' s x'' f)). Qed.
Lemma lem3467831 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : ((term442 _89991 _90000 x x' s x'' f) = (term443 _89991 _90000 x x' s x'' f)) = ((term436 _89991 _90000 x x' s x'' f) = (term453 _89991 _90000 x x' s x'' f)).
Proof. exact (MK_COMB (@lem3467824 _89991 _90000 x x' s x'' f) (@lem3467830 _89991 _90000 x x' s x'' f)). Qed.
Lemma lem3467832 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term436 _89991 _90000 x x' s x'' f) = (term453 _89991 _90000 x x' s x'' f).
Proof. exact (EQ_MP (@lem3467831 _89991 _90000 x x' s x'' f) (@lem3467816 _89991 _90000 x x' s x'' f)). Qed.
Lemma lem3467834 {A : Type'} (P : Prop) (Q : A -> Prop) : (term290 A P Q) = (term291 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3467835 {_89991 : Type'} (P : Prop) (Q : type162 _89991) : (term454 _89991 P Q) = (term455 _89991 P Q).
Proof. exact (@lem3467834 (type684 _89991) P Q). Qed.
Lemma lem3467836 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term456 _89991 _90000 x x' t s x'' f) = (term457 _89991 _90000 x x' t s x'' f).
Proof. exact (@lem3467835 _89991 (term283 _89991 _90000 x s x'' f x') (term401 _89991 _90000 t s x'' f)). Qed.
Lemma lem3467837 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) : (term458 _89991 _90000 t s x f x') = (term399 _89991 _90000 t s x f x').
Proof. exact (eq_refl (term458 _89991 _90000 t s x f x')). Qed.
Lemma lem3467838 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term459 _89991 _90000 t s x f) = (term401 _89991 _90000 t s x f).
Proof. exact (fun_ext (fun x' : type684 _89991 => @lem3467837 _89991 _90000 t s x f x')). Qed.
Lemma lem3467839 {_89991 : Type'} : (@ex ((_89991 -> Prop) -> _89991)) = (@ex ((_89991 -> Prop) -> _89991)).
Proof. exact (eq_refl (@ex ((_89991 -> Prop) -> _89991))). Qed.
Lemma lem3467840 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term460 _89991 _90000 t s x f) = (term402 _89991 _90000 t s x f).
Proof. exact (MK_COMB (@lem3467839 _89991) (@lem3467838 _89991 _90000 t s x f)). Qed.
Lemma lem3467841 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term434 _89991 _90000 x s x' f x'') = (term434 _89991 _90000 x s x' f x'').
Proof. exact (eq_refl (term434 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467842 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term456 _89991 _90000 x x' t s x'' f) = (term450 _89991 _90000 x x' t s x'' f).
Proof. exact (MK_COMB (@lem3467841 _89991 _90000 x s x'' f x') (@lem3467840 _89991 _90000 t s x'' f)). Qed.
Lemma lem3467843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3467844 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term461 _89991 _90000 x x' t s x'' f) = (term462 _89991 _90000 x x' t s x'' f).
Proof. exact (MK_COMB (@lem3467843) (@lem3467842 _89991 _90000 x x' t s x'' f)). Qed.
Lemma lem3467845 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x' : type684 _89991) : (term458 _89991 _90000 t s x f x') = (term399 _89991 _90000 t s x f x').
Proof. exact (eq_refl (term458 _89991 _90000 t s x f x')). Qed.
Lemma lem3467846 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term434 _89991 _90000 x s x' f x'') = (term434 _89991 _90000 x s x' f x'').
Proof. exact (eq_refl (term434 _89991 _90000 x s x' f x'')). Qed.
Lemma lem3467847 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) : (term463 _89991 _90000 x x' t s x'' f x''') = (term464 _89991 _90000 x x' t s x'' f x''').
Proof. exact (MK_COMB (@lem3467846 _89991 _90000 x s x'' f x') (@lem3467845 _89991 _90000 t s x'' f x''')). Qed.
Lemma lem3467848 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term465 _89991 _90000 x x' t s x'' f) = (term466 _89991 _90000 x x' t s x'' f).
Proof. exact (fun_ext (fun x''' : type684 _89991 => @lem3467847 _89991 _90000 x x' t s x'' f x''')). Qed.
Lemma lem3467849 {_89991 : Type'} : (@ex ((_89991 -> Prop) -> _89991)) = (@ex ((_89991 -> Prop) -> _89991)).
Proof. exact (eq_refl (@ex ((_89991 -> Prop) -> _89991))). Qed.
Lemma lem3467850 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term457 _89991 _90000 x x' t s x'' f) = (term467 _89991 _90000 x x' t s x'' f).
Proof. exact (MK_COMB (@lem3467849 _89991) (@lem3467848 _89991 _90000 x x' t s x'' f)). Qed.
Lemma lem3467851 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : ((term456 _89991 _90000 x x' t s x'' f) = (term457 _89991 _90000 x x' t s x'' f)) = ((term450 _89991 _90000 x x' t s x'' f) = (term467 _89991 _90000 x x' t s x'' f)).
Proof. exact (MK_COMB (@lem3467844 _89991 _90000 x x' t s x'' f) (@lem3467850 _89991 _90000 x x' t s x'' f)). Qed.
Lemma lem3467852 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term450 _89991 _90000 x x' t s x'' f) = (term467 _89991 _90000 x x' t s x'' f).
Proof. exact (EQ_MP (@lem3467851 _89991 _90000 x x' t s x'' f) (@lem3467836 _89991 _90000 x x' t s x'' f)). Qed.
Lemma lem3467853 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term452 _89991 _90000 x x' s x'' f) = (term468 _89991 _90000 x x' s x'' f).
Proof. exact (fun_ext (fun t : type1402 _89991 => @lem3467852 _89991 _90000 x x' t s x'' f)). Qed.
Lemma lem3467854 {_89991 : Type'} : (@ex (_89991 -> _89991 -> Prop)) = (@ex (_89991 -> _89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> _89991 -> Prop))). Qed.
Lemma lem3467855 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term453 _89991 _90000 x x' s x'' f) = (term469 _89991 _90000 x x' s x'' f).
Proof. exact (MK_COMB (@lem3467854 _89991) (@lem3467853 _89991 _90000 x x' s x'' f)). Qed.
Lemma lem3467856 {_89991 _90000 : Type'} (x : _89991) (x' : _89991 -> Prop) (s : type686 _89991) (x'' : _90000) (f : _89991 -> _90000) : (term436 _89991 _90000 x x' s x'' f) = (term469 _89991 _90000 x x' s x'' f).
Proof. exact (TRANS (@lem3467832 _89991 _90000 x x' s x'' f) (@lem3467855 _89991 _90000 x x' s x'' f)). Qed.
Lemma lem3467857 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term438 _89991 _90000 x s x' f) = (term470 _89991 _90000 x s x' f).
Proof. exact (fun_ext (fun x'' : _89991 -> Prop => @lem3467856 _89991 _90000 x x'' s x' f)). Qed.
Lemma lem3467858 {_89991 : Type'} : (@ex (_89991 -> Prop)) = (@ex (_89991 -> Prop)).
Proof. exact (eq_refl (@ex (_89991 -> Prop))). Qed.
Lemma lem3467859 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term439 _89991 _90000 x s x' f) = (term471 _89991 _90000 x s x' f).
Proof. exact (MK_COMB (@lem3467858 _89991) (@lem3467857 _89991 _90000 x s x' f)). Qed.
Lemma lem3467860 {_89991 _90000 : Type'} (x : _89991) (s : type686 _89991) (x' : _90000) (f : _89991 -> _90000) : (term419 _89991 _90000 x s x' f) = (term471 _89991 _90000 x s x' f).
Proof. exact (TRANS (@lem3467812 _89991 _90000 x s x' f) (@lem3467859 _89991 _90000 x s x' f)). Qed.
Lemma lem3467861 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term421 _89991 _90000 s x f) = (term472 _89991 _90000 s x f).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467860 _89991 _90000 x' s x f)). Qed.
Lemma lem3467862 {_89991 : Type'} : (@ex _89991) = (@ex _89991).
Proof. exact (eq_refl (@ex _89991)). Qed.
Lemma lem3467863 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term422 _89991 _90000 s x f) = (term473 _89991 _90000 s x f).
Proof. exact (MK_COMB (@lem3467862 _89991) (@lem3467861 _89991 _90000 s x f)). Qed.
Lemma lem3467864 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term405 _89991 _90000 s x f) = (term473 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467786 _89991 _90000 s x f) (@lem3467863 _89991 _90000 s x f)). Qed.
Lemma lem3467866 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term255 _89991 _90000 s x f) = (term473 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467760 _89991 _90000 s x f) (@lem3467864 _89991 _90000 s x f)). Qed.
Lemma lem3467867 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) : (term149 _89991 _90000 s x f) = (term473 _89991 _90000 s x f).
Proof. exact (TRANS (@lem3467220 _89991 _90000 s x f) (@lem3467866 _89991 _90000 s x f)). Qed.
Lemma lem3467868 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (h1 : term149 _89991 _90000 s x f) : term473 _89991 _90000 s x f.
Proof. exact (EQ_MP (@lem3467867 _89991 _90000 s x f) (@lem3466876 _89991 _90000 s x f h1)). Qed.
Lemma lem3467869 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (h1 : term471 _89991 _90000 x' s x f) : term471 _89991 _90000 x' s x f.
Proof. exact (h1). Qed.
Lemma lem3467870 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (h1 : term469 _89991 _90000 x' x'' s x f) : term469 _89991 _90000 x' x'' s x f.
Proof. exact (h1). Qed.
Lemma lem3467871 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (h1 : term467 _89991 _90000 x' x'' t s x f) : term467 _89991 _90000 x' x'' t s x f.
Proof. exact (h1). Qed.
Lemma lem3467872 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term464 _89991 _90000 x' x'' t s x f x''') : term464 _89991 _90000 x' x'' t s x f x'''.
Proof. exact (h1). Qed.
Lemma lem3467873 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term474 _89991 _90000 x'''' s f.
Proof. exact (h1). Qed.
Lemma lem3467874 {_89991 : Type'} (x : _89991 -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3467879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467880 {_89991 : Type'} (f : type684 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> _89991) f x).
Proof. exact (@lem3467879 (_89991 -> Prop) _89991 f x). Qed.
Lemma lem3467882 {_89991 : Type'} (x''' : type684 _89991) (x : _89991 -> Prop) : (x''' x) = (@I ((_89991 -> Prop) -> _89991) x''' x).
Proof. exact (@lem3467880 _89991 x''' x). Qed.
Lemma lem3467883 {_89991 : Type'} (x''' : type684 _89991) (x : _89991 -> Prop) : (term475 _89991 x''' x) = (term476 _89991 x''' x).
Proof. exact (MK_COMB (@lem3467874 _89991 x) (@lem3467882 _89991 x''' x)). Qed.
Lemma lem3467885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467886 {_89991 : Type'} (f : _89991 -> Prop) (x : _89991) : (f x) = (@I (_89991 -> Prop) f x).
Proof. exact (@lem3467885 _89991 Prop f x). Qed.
Lemma lem3467887 {_89991 : Type'} (x''' : type684 _89991) (x : _89991 -> Prop) : (term476 _89991 x''' x) = (term477 _89991 x''' x).
Proof. exact (@lem3467886 _89991 x (@I ((_89991 -> Prop) -> _89991) x''' x)). Qed.
Lemma lem3467888 {_89991 : Type'} (x''' : type684 _89991) (x : _89991 -> Prop) : (term475 _89991 x''' x) = (term477 _89991 x''' x).
Proof. exact (TRANS (@lem3467883 _89991 x''' x) (@lem3467887 _89991 x''' x)). Qed.
Lemma lem3467891 {_89991 _90000 : Type'} (f : _89991 -> _90000) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3467896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467897 {_89991 : Type'} (f : type684 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> _89991) f x).
Proof. exact (@lem3467896 (_89991 -> Prop) _89991 f x). Qed.
Lemma lem3467899 {_89991 : Type'} (x''' : type684 _89991) (x : _89991 -> Prop) : (x''' x) = (@I ((_89991 -> Prop) -> _89991) x''' x).
Proof. exact (@lem3467897 _89991 x''' x). Qed.
Lemma lem3467900 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x''' : type684 _89991) (x : _89991 -> Prop) : (term478 _89991 _90000 f x''' x) = (term479 _89991 _90000 f x''' x).
Proof. exact (MK_COMB (@lem3467891 _89991 _90000 f) (@lem3467899 _89991 x''' x)). Qed.
Lemma lem3467902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467903 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x : _89991) : (f x) = (@I (_89991 -> _90000) f x).
Proof. exact (@lem3467902 _89991 _90000 f x). Qed.
Lemma lem3467904 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x''' : type684 _89991) (x : _89991 -> Prop) : (term479 _89991 _90000 f x''' x) = (term480 _89991 _90000 f x''' x).
Proof. exact (@lem3467903 _89991 _90000 f (@I ((_89991 -> Prop) -> _89991) x''' x)). Qed.
Lemma lem3467905 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x''' : type684 _89991) (x : _89991 -> Prop) : (term478 _89991 _90000 f x''' x) = (term480 _89991 _90000 f x''' x).
Proof. exact (TRANS (@lem3467900 _89991 _90000 f x''' x) (@lem3467904 _89991 _90000 f x''' x)). Qed.
Lemma lem3467906 {_90000 : Type'} (x : _90000) : (@eq _90000 x) = (@eq _90000 x).
Proof. exact (eq_refl (@eq _90000 x)). Qed.
Lemma lem3467907 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x' : _89991 -> Prop) : (x = (term478 _89991 _90000 f x''' x')) = (x = (term480 _89991 _90000 f x''' x')).
Proof. exact (MK_COMB (@lem3467906 _90000 x) (@lem3467905 _89991 _90000 f x''' x')). Qed.
Lemma lem3467908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467909 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x' : _89991 -> Prop) : (term481 _89991 _90000 x f x''' x') = (term482 _89991 _90000 x f x''' x').
Proof. exact (MK_COMB (@lem3467908) (@lem3467907 _89991 _90000 x f x''' x')). Qed.
Lemma lem3467910 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x' : _89991 -> Prop) : (term483 _89991 _90000 x f x''' x') = (term484 _89991 _90000 x f x''' x').
Proof. exact (MK_COMB (@lem3467909 _89991 _90000 x f x''' x') (@lem3467888 _89991 x''' x')). Qed.
Lemma lem3467911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467916 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467917 {_89991 : Type'} (f : type686 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> Prop) f x).
Proof. exact (@lem3467916 (_89991 -> Prop) Prop f x). Qed.
Lemma lem3467919 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (s x) = (@I ((_89991 -> Prop) -> Prop) s x).
Proof. exact (@lem3467917 _89991 s x). Qed.
Lemma lem3467920 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term48 _89991 s x) = (term485 _89991 s x).
Proof. exact (MK_COMB (@lem3467911) (@lem3467919 _89991 s x)). Qed.
Lemma lem3467921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467922 {_89991 : Type'} (s : type686 _89991) (x : _89991 -> Prop) : (term233 _89991 s x) = (term486 _89991 s x).
Proof. exact (MK_COMB (@lem3467921) (@lem3467920 _89991 s x)). Qed.
Lemma lem3467923 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x' : _89991 -> Prop) : (term363 _89991 _90000 s x f x''' x') = (term487 _89991 _90000 s x f x''' x').
Proof. exact (MK_COMB (@lem3467922 _89991 s x') (@lem3467910 _89991 _90000 x f x''' x')). Qed.
Lemma lem3467924 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) : (term365 _89991 _90000 s x f x''') = (term488 _89991 _90000 s x f x''').
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3467923 _89991 _90000 s x f x''' x')). Qed.
Lemma lem3467925 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3467926 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) : (term367 _89991 _90000 s x f x''') = (term489 _89991 _90000 s x f x''').
Proof. exact (MK_COMB (@lem3467925 _89991) (@lem3467924 _89991 _90000 s x f x''')). Qed.
Lemma lem3467927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467935 {_89991 : Type'} (f : type1402 _89991) (x : _89991) : (f x) = (@I (_89991 -> _89991 -> Prop) f x).
Proof. exact (@lem3467934 _89991 (_89991 -> Prop) f x). Qed.
Lemma lem3467936 {_89991 : Type'} (t : type1402 _89991) (x : _89991) : (t x) = (@I (_89991 -> _89991 -> Prop) t x).
Proof. exact (@lem3467935 _89991 t x). Qed.
Lemma lem3467937 {_89991 : Type'} (x : _89991) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3467938 {_89991 : Type'} (t : type1402 _89991) (x : _89991) : (t x x) = (@I (_89991 -> _89991 -> Prop) t x x).
Proof. exact (MK_COMB (@lem3467936 _89991 t x) (@lem3467937 _89991 x)). Qed.
Lemma lem3467940 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467941 {_89991 : Type'} (f : _89991 -> Prop) (x : _89991) : (f x) = (@I (_89991 -> Prop) f x).
Proof. exact (@lem3467940 _89991 Prop f x). Qed.
Lemma lem3467942 {_89991 : Type'} (t : type1402 _89991) (x : _89991) : (@I (_89991 -> _89991 -> Prop) t x x) = (term490 _89991 t x).
Proof. exact (@lem3467941 _89991 (@I (_89991 -> _89991 -> Prop) t x) x). Qed.
Lemma lem3467944 {_89991 : Type'} (t : type1402 _89991) (x : _89991) : (t x x) = (term490 _89991 t x).
Proof. exact (TRANS (@lem3467938 _89991 t x) (@lem3467942 _89991 t x)). Qed.
Lemma lem3467945 {_89991 : Type'} (t : type1402 _89991) (x : _89991) : (term491 _89991 t x) = (term492 _89991 t x).
Proof. exact (MK_COMB (@lem3467927) (@lem3467944 _89991 t x)). Qed.
Lemma lem3467946 {_89991 : Type'} (s : type686 _89991) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3467951 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467952 {_89991 : Type'} (f : type1402 _89991) (x : _89991) : (f x) = (@I (_89991 -> _89991 -> Prop) f x).
Proof. exact (@lem3467951 _89991 (_89991 -> Prop) f x). Qed.
Lemma lem3467954 {_89991 : Type'} (t : type1402 _89991) (x : _89991) : (t x) = (@I (_89991 -> _89991 -> Prop) t x).
Proof. exact (@lem3467952 _89991 t x). Qed.
Lemma lem3467955 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _89991) : (term493 _89991 s t x) = (term494 _89991 s t x).
Proof. exact (MK_COMB (@lem3467946 _89991 s) (@lem3467954 _89991 t x)). Qed.
Lemma lem3467957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467958 {_89991 : Type'} (f : type686 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> Prop) f x).
Proof. exact (@lem3467957 (_89991 -> Prop) Prop f x). Qed.
Lemma lem3467959 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _89991) : (term494 _89991 s t x) = (term495 _89991 s t x).
Proof. exact (@lem3467958 _89991 s (@I (_89991 -> _89991 -> Prop) t x)). Qed.
Lemma lem3467960 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _89991) : (term493 _89991 s t x) = (term495 _89991 s t x).
Proof. exact (TRANS (@lem3467955 _89991 s t x) (@lem3467959 _89991 s t x)). Qed.
Lemma lem3467961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467962 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _89991) : (term496 _89991 s t x) = (term497 _89991 s t x).
Proof. exact (MK_COMB (@lem3467961) (@lem3467960 _89991 s t x)). Qed.
Lemma lem3467963 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _89991) : (term498 _89991 s t x) = (term499 _89991 s t x).
Proof. exact (MK_COMB (@lem3467962 _89991 s t x) (@lem3467945 _89991 t x)). Qed.
Lemma lem3467964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467971 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467973 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x : _89991) : (f x) = (@I (_89991 -> _90000) f x).
Proof. exact (@lem3467971 _89991 _90000 f x). Qed.
Lemma lem3467974 {_90000 : Type'} (x : _90000) : (@eq _90000 x) = (@eq _90000 x).
Proof. exact (eq_refl (@eq _90000 x)). Qed.
Lemma lem3467975 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (x = (f x')) = (x = (@I (_89991 -> _90000) f x')).
Proof. exact (MK_COMB (@lem3467974 _90000 x) (@lem3467973 _89991 _90000 f x')). Qed.
Lemma lem3467976 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term296 _89991 _90000 x f x') = (term500 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3467964) (@lem3467975 _89991 _90000 x f x')). Qed.
Lemma lem3467977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3467978 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term205 _89991 _90000 x f x') = (term501 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3467977) (@lem3467976 _89991 _90000 x f x')). Qed.
Lemma lem3467979 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) (x' : _89991) : (term326 _89991 _90000 x f s t x') = (term502 _89991 _90000 x f s t x').
Proof. exact (MK_COMB (@lem3467978 _89991 _90000 x f x') (@lem3467963 _89991 s t x')). Qed.
Lemma lem3467980 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term328 _89991 _90000 x f s t) = (term503 _89991 _90000 x f s t).
Proof. exact (fun_ext (fun x' : _89991 => @lem3467979 _89991 _90000 x f s t x')). Qed.
Lemma lem3467981 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3467982 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term330 _89991 _90000 x f s t) = (term504 _89991 _90000 x f s t).
Proof. exact (MK_COMB (@lem3467981 _89991) (@lem3467980 _89991 _90000 x f s t)). Qed.
Lemma lem3467983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3467984 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) : (term383 _89991 _90000 x f s t) = (term505 _89991 _90000 x f s t).
Proof. exact (MK_COMB (@lem3467983) (@lem3467982 _89991 _90000 x f s t)). Qed.
Lemma lem3467985 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) : (term399 _89991 _90000 t s x f x''') = (term506 _89991 _90000 t s x f x''').
Proof. exact (MK_COMB (@lem3467984 _89991 _90000 x f s t) (@lem3467926 _89991 _90000 s x f x''')). Qed.
Lemma lem3467986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3467991 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3467992 {_89991 : Type'} (f : _89991 -> Prop) (x : _89991) : (f x) = (@I (_89991 -> Prop) f x).
Proof. exact (@lem3467991 _89991 Prop f x). Qed.
Lemma lem3467994 {_89991 : Type'} (x'' : _89991 -> Prop) (x : _89991) : (x'' x) = (@I (_89991 -> Prop) x'' x).
Proof. exact (@lem3467992 _89991 x'' x). Qed.
Lemma lem3467995 {_89991 : Type'} (x'' : _89991 -> Prop) (x : _89991) : (term507 _89991 x'' x) = (term508 _89991 x'' x).
Proof. exact (MK_COMB (@lem3467986) (@lem3467994 _89991 x'' x)). Qed.
Lemma lem3467996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3468003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468005 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x : _89991) : (f x) = (@I (_89991 -> _90000) f x).
Proof. exact (@lem3468003 _89991 _90000 f x). Qed.
Lemma lem3468006 {_90000 : Type'} (x : _90000) : (@eq _90000 x) = (@eq _90000 x).
Proof. exact (eq_refl (@eq _90000 x)). Qed.
Lemma lem3468007 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (x = (f x')) = (x = (@I (_89991 -> _90000) f x')).
Proof. exact (MK_COMB (@lem3468006 _90000 x) (@lem3468005 _89991 _90000 f x')). Qed.
Lemma lem3468008 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term296 _89991 _90000 x f x') = (term500 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3467996) (@lem3468007 _89991 _90000 x f x')). Qed.
Lemma lem3468009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468010 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term205 _89991 _90000 x f x') = (term501 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3468009) (@lem3468008 _89991 _90000 x f x')). Qed.
Lemma lem3468011 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (x' : _89991) : (term222 _89991 _90000 x f x'' x') = (term509 _89991 _90000 x f x'' x').
Proof. exact (MK_COMB (@lem3468010 _89991 _90000 x f x') (@lem3467995 _89991 x'' x')). Qed.
Lemma lem3468012 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term228 _89991 _90000 x f x'') = (term510 _89991 _90000 x f x'').
Proof. exact (fun_ext (fun x' : _89991 => @lem3468011 _89991 _90000 x f x'' x')). Qed.
Lemma lem3468013 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468014 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term229 _89991 _90000 x f x'') = (term511 _89991 _90000 x f x'').
Proof. exact (MK_COMB (@lem3468013 _89991) (@lem3468012 _89991 _90000 x f x'')). Qed.
Lemma lem3468019 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468020 {_89991 : Type'} (f : type686 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> Prop) f x).
Proof. exact (@lem3468019 (_89991 -> Prop) Prop f x). Qed.
Lemma lem3468022 {_89991 : Type'} (s : type686 _89991) (x'' : _89991 -> Prop) : (s x'') = (@I ((_89991 -> Prop) -> Prop) s x'').
Proof. exact (@lem3468020 _89991 s x''). Qed.
Lemma lem3468023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3468024 {_89991 : Type'} (s : type686 _89991) (x'' : _89991 -> Prop) : (term57 _89991 s x'') = (term512 _89991 s x'').
Proof. exact (MK_COMB (@lem3468023) (@lem3468022 _89991 s x'')). Qed.
Lemma lem3468025 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term231 _89991 _90000 s x f x'') = (term513 _89991 _90000 s x f x'').
Proof. exact (MK_COMB (@lem3468024 _89991 s x'') (@lem3468014 _89991 _90000 x f x'')). Qed.
Lemma lem3468030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468031 {_89991 : Type'} (f : _89991 -> Prop) (x : _89991) : (f x) = (@I (_89991 -> Prop) f x).
Proof. exact (@lem3468030 _89991 Prop f x). Qed.
Lemma lem3468033 {_89991 : Type'} (t : _89991 -> Prop) (x' : _89991) : (t x') = (@I (_89991 -> Prop) t x').
Proof. exact (@lem3468031 _89991 t x'). Qed.
Lemma lem3468034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3468039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468040 {_89991 : Type'} (f : type686 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> Prop) f x).
Proof. exact (@lem3468039 (_89991 -> Prop) Prop f x). Qed.
Lemma lem3468042 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (s t) = (@I ((_89991 -> Prop) -> Prop) s t).
Proof. exact (@lem3468040 _89991 s t). Qed.
Lemma lem3468043 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term48 _89991 s t) = (term485 _89991 s t).
Proof. exact (MK_COMB (@lem3468034) (@lem3468042 _89991 s t)). Qed.
Lemma lem3468044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468045 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term233 _89991 s t) = (term486 _89991 s t).
Proof. exact (MK_COMB (@lem3468044) (@lem3468043 _89991 s t)). Qed.
Lemma lem3468046 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x' : _89991) : (term195 _89991 s t x') = (term514 _89991 s t x').
Proof. exact (MK_COMB (@lem3468045 _89991 s t) (@lem3468033 _89991 t x')). Qed.
Lemma lem3468047 {_89991 : Type'} (s : type686 _89991) (x' : _89991) : (term203 _89991 s x') = (term515 _89991 s x').
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468046 _89991 s t x')). Qed.
Lemma lem3468048 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468049 {_89991 : Type'} (s : type686 _89991) (x' : _89991) : (term204 _89991 s x') = (term516 _89991 s x').
Proof. exact (MK_COMB (@lem3468048 _89991) (@lem3468047 _89991 s x')). Qed.
Lemma lem3468056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468057 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x : _89991) : (f x) = (@I (_89991 -> _90000) f x).
Proof. exact (@lem3468056 _89991 _90000 f x). Qed.
Lemma lem3468059 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x' : _89991) : (f x') = (@I (_89991 -> _90000) f x').
Proof. exact (@lem3468057 _89991 _90000 f x'). Qed.
Lemma lem3468060 {_90000 : Type'} (x : _90000) : (@eq _90000 x) = (@eq _90000 x).
Proof. exact (eq_refl (@eq _90000 x)). Qed.
Lemma lem3468061 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (x = (f x')) = (x = (@I (_89991 -> _90000) f x')).
Proof. exact (MK_COMB (@lem3468060 _90000 x) (@lem3468059 _89991 _90000 f x')). Qed.
Lemma lem3468062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3468063 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x' : _89991) : (term95 _89991 _90000 x f x') = (term517 _89991 _90000 x f x').
Proof. exact (MK_COMB (@lem3468062) (@lem3468061 _89991 _90000 x f x')). Qed.
Lemma lem3468064 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term209 _89991 _90000 x f s x') = (term518 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3468063 _89991 _90000 x f x') (@lem3468049 _89991 s x')). Qed.
Lemma lem3468065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3468066 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x' : _89991) : (term265 _89991 _90000 x f s x') = (term519 _89991 _90000 x f s x').
Proof. exact (MK_COMB (@lem3468065) (@lem3468064 _89991 _90000 x f s x')). Qed.
Lemma lem3468067 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term283 _89991 _90000 x' s x f x'') = (term520 _89991 _90000 x' s x f x'').
Proof. exact (MK_COMB (@lem3468066 _89991 _90000 x f s x') (@lem3468025 _89991 _90000 s x f x'')). Qed.
Lemma lem3468068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468069 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term434 _89991 _90000 x' s x f x'') = (term521 _89991 _90000 x' s x f x'').
Proof. exact (MK_COMB (@lem3468068) (@lem3468067 _89991 _90000 x' s x f x'')). Qed.
Lemma lem3468070 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) : (term464 _89991 _90000 x' x'' t s x f x''') = (term522 _89991 _90000 x' x'' t s x f x''').
Proof. exact (MK_COMB (@lem3468069 _89991 _90000 x' s x f x'') (@lem3467985 _89991 _90000 t s x f x''')). Qed.
Lemma lem3468071 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term464 _89991 _90000 x' x'' t s x f x''') : term522 _89991 _90000 x' x'' t s x f x'''.
Proof. exact (EQ_MP (@lem3468070 _89991 _90000 x' x'' t s x f x''') (@lem3467872 _89991 _90000 x' x'' t s x f x''' h1)). Qed.
Lemma lem3468076 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3468077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3468078 {_90000 : Type'} : (@eq _90000) = (@eq _90000).
Proof. exact (eq_refl (@eq _90000)). Qed.
Lemma lem3468083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468085 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x : _89991) : (f x) = (@I (_89991 -> _90000) f x).
Proof. exact (@lem3468083 _89991 _90000 f x). Qed.
Lemma lem3468090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468091 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x : _89991) : (f x) = (@I (_89991 -> _90000) f x).
Proof. exact (@lem3468090 _89991 _90000 f x). Qed.
Lemma lem3468093 {_89991 _90000 : Type'} (f : _89991 -> _90000) (y : _89991) : (f y) = (@I (_89991 -> _90000) f y).
Proof. exact (@lem3468091 _89991 _90000 f y). Qed.
Lemma lem3468094 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x : _89991) : (term523 _89991 _90000 f x) = (term524 _89991 _90000 f x).
Proof. exact (MK_COMB (@lem3468078 _90000) (@lem3468085 _89991 _90000 f x)). Qed.
Lemma lem3468095 {_89991 _90000 : Type'} (x : _89991) (f : _89991 -> _90000) (y : _89991) : ((f x) = (f y)) = ((@I (_89991 -> _90000) f x) = (@I (_89991 -> _90000) f y)).
Proof. exact (MK_COMB (@lem3468094 _89991 _90000 f x) (@lem3468093 _89991 _90000 f y)). Qed.
Lemma lem3468096 {_89991 _90000 : Type'} (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term169 _89991 _90000 x f y) = (term525 _89991 _90000 x f y).
Proof. exact (MK_COMB (@lem3468077) (@lem3468095 _89991 _90000 x f y)). Qed.
Lemma lem3468097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3468102 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468103 {_89991 : Type'} (f : _89991 -> Prop) (x : _89991) : (f x) = (@I (_89991 -> Prop) f x).
Proof. exact (@lem3468102 _89991 Prop f x). Qed.
Lemma lem3468105 {_89991 : Type'} (t : _89991 -> Prop) (y : _89991) : (t y) = (@I (_89991 -> Prop) t y).
Proof. exact (@lem3468103 _89991 t y). Qed.
Lemma lem3468106 {_89991 : Type'} (t : _89991 -> Prop) (y : _89991) : (term507 _89991 t y) = (term508 _89991 t y).
Proof. exact (MK_COMB (@lem3468097) (@lem3468105 _89991 t y)). Qed.
Lemma lem3468107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3468112 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468113 {_89991 : Type'} (f : type686 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> Prop) f x).
Proof. exact (@lem3468112 (_89991 -> Prop) Prop f x). Qed.
Lemma lem3468115 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (s t) = (@I ((_89991 -> Prop) -> Prop) s t).
Proof. exact (@lem3468113 _89991 s t). Qed.
Lemma lem3468116 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term48 _89991 s t) = (term485 _89991 s t).
Proof. exact (MK_COMB (@lem3468107) (@lem3468115 _89991 s t)). Qed.
Lemma lem3468117 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468118 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term233 _89991 s t) = (term486 _89991 s t).
Proof. exact (MK_COMB (@lem3468117) (@lem3468116 _89991 s t)). Qed.
Lemma lem3468119 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term160 _89991 s t y) = (term526 _89991 s t y).
Proof. exact (MK_COMB (@lem3468118 _89991 s t) (@lem3468106 _89991 t y)). Qed.
Lemma lem3468120 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term167 _89991 s y) = (term527 _89991 s y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468119 _89991 s t y)). Qed.
Lemma lem3468121 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468122 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term168 _89991 s y) = (term528 _89991 s y).
Proof. exact (MK_COMB (@lem3468121 _89991) (@lem3468120 _89991 s y)). Qed.
Lemma lem3468123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468124 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term171 _89991 s y) = (term529 _89991 s y).
Proof. exact (MK_COMB (@lem3468123) (@lem3468122 _89991 s y)). Qed.
Lemma lem3468125 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term173 _89991 _90000 s x f y) = (term530 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468124 _89991 s y) (@lem3468096 _89991 _90000 x f y)). Qed.
Lemma lem3468126 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3468131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468132 {_89991 : Type'} (f : _89991 -> Prop) (x : _89991) : (f x) = (@I (_89991 -> Prop) f x).
Proof. exact (@lem3468131 _89991 Prop f x). Qed.
Lemma lem3468134 {_89991 : Type'} (t : _89991 -> Prop) (x : _89991) : (t x) = (@I (_89991 -> Prop) t x).
Proof. exact (@lem3468132 _89991 t x). Qed.
Lemma lem3468135 {_89991 : Type'} (t : _89991 -> Prop) (x : _89991) : (term507 _89991 t x) = (term508 _89991 t x).
Proof. exact (MK_COMB (@lem3468126) (@lem3468134 _89991 t x)). Qed.
Lemma lem3468136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3468141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468142 {_89991 : Type'} (f : type686 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> Prop) f x).
Proof. exact (@lem3468141 (_89991 -> Prop) Prop f x). Qed.
Lemma lem3468144 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (s t) = (@I ((_89991 -> Prop) -> Prop) s t).
Proof. exact (@lem3468142 _89991 s t). Qed.
Lemma lem3468145 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term48 _89991 s t) = (term485 _89991 s t).
Proof. exact (MK_COMB (@lem3468136) (@lem3468144 _89991 s t)). Qed.
Lemma lem3468146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468147 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) : (term233 _89991 s t) = (term486 _89991 s t).
Proof. exact (MK_COMB (@lem3468146) (@lem3468145 _89991 s t)). Qed.
Lemma lem3468148 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term160 _89991 s t x) = (term526 _89991 s t x).
Proof. exact (MK_COMB (@lem3468147 _89991 s t) (@lem3468135 _89991 t x)). Qed.
Lemma lem3468149 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term167 _89991 s x) = (term527 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468148 _89991 s t x)). Qed.
Lemma lem3468150 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468151 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term168 _89991 s x) = (term528 _89991 s x).
Proof. exact (MK_COMB (@lem3468150 _89991) (@lem3468149 _89991 s x)). Qed.
Lemma lem3468152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468153 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term171 _89991 s x) = (term529 _89991 s x).
Proof. exact (MK_COMB (@lem3468152) (@lem3468151 _89991 s x)). Qed.
Lemma lem3468154 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term176 _89991 _90000 s x f y) = (term531 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468153 _89991 s x) (@lem3468125 _89991 _90000 s x f y)). Qed.
Lemma lem3468155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468156 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term179 _89991 _90000 s x f y) = (term532 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468155) (@lem3468154 _89991 _90000 s x f y)). Qed.
Lemma lem3468157 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term181 _89991 _90000 s f x y) = (term533 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3468156 _89991 _90000 s x f y) (@lem3468076 _89991 x y)). Qed.
Lemma lem3468158 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term182 _89991 _90000 s f x) = (term534 _89991 _90000 s f x).
Proof. exact (fun_ext (fun y : _89991 => @lem3468157 _89991 _90000 s f x y)). Qed.
Lemma lem3468159 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468160 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term183 _89991 _90000 s f x) = (term535 _89991 _90000 s f x).
Proof. exact (MK_COMB (@lem3468159 _89991) (@lem3468158 _89991 _90000 s f x)). Qed.
Lemma lem3468161 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term184 _89991 _90000 s f) = (term536 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _89991 => @lem3468160 _89991 _90000 s f x)). Qed.
Lemma lem3468162 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468163 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term185 _89991 _90000 s f) = (term537 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3468162 _89991) (@lem3468161 _89991 _90000 s f)). Qed.
Lemma lem3468168 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3468169 {_89991 : Type'} (f : type686 _89991) (x : _89991 -> Prop) : (f x) = (@I ((_89991 -> Prop) -> Prop) f x).
Proof. exact (@lem3468168 (_89991 -> Prop) Prop f x). Qed.
Lemma lem3468171 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3468169 _89991 s x''''). Qed.
Lemma lem3468172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3468173 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term57 _89991 s x'''') = (term512 _89991 s x'''').
Proof. exact (MK_COMB (@lem3468172) (@lem3468171 _89991 s x'''')). Qed.
Lemma lem3468174 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) : (term474 _89991 _90000 x'''' s f) = (term538 _89991 _90000 x'''' s f).
Proof. exact (MK_COMB (@lem3468173 _89991 s x'''') (@lem3468163 _89991 _90000 s f)). Qed.
Lemma lem3468175 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term538 _89991 _90000 x'''' s f.
Proof. exact (EQ_MP (@lem3468174 _89991 _90000 x'''' s f) (@lem3467873 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3468176 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term537 _89991 _90000 s f.
Proof. exact (proj2 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3468178 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term520 _89991 _90000 x' s x f x''.
Proof. exact (h1). Qed.
Lemma lem3468179 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term506 _89991 _90000 t s x f x'''.
Proof. exact (h1). Qed.
Lemma lem3468180 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term513 _89991 _90000 s x f x''.
Proof. exact (proj2 (@lem3468178 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468181 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term518 _89991 _90000 x f s x'.
Proof. exact (proj1 (@lem3468178 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468182 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term511 _89991 _90000 x f x''.
Proof. exact (proj2 (@lem3468180 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468184 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term516 _89991 s x'.
Proof. exact (proj2 (@lem3468181 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468186 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term489 _89991 _90000 s x f x'''.
Proof. exact (proj2 (@lem3468179 _89991 _90000 t s x f x''' h1)). Qed.
Lemma lem3468187 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term504 _89991 _90000 x f s t.
Proof. exact (proj1 (@lem3468179 _89991 _90000 t s x f x''' h1)). Qed.
Lemma lem3468386 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (x' : _89991) : (term509 _89991 _90000 x f x'' x') = (term509 _89991 _90000 x f x'' x').
Proof. exact (eq_refl (term509 _89991 _90000 x f x'' x')). Qed.
Lemma lem3468387 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term510 _89991 _90000 x f x'') = (term510 _89991 _90000 x f x'').
Proof. exact (fun_ext (fun x' : _89991 => @lem3468386 _89991 _90000 x f x'' x')). Qed.
Lemma lem3468388 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468390 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) : (term511 _89991 _90000 x f x'') = (term511 _89991 _90000 x f x'').
Proof. exact (MK_COMB (@lem3468388 _89991) (@lem3468387 _89991 _90000 x f x'')). Qed.
Lemma lem3468391 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term511 _89991 _90000 x f x''.
Proof. exact (EQ_MP (@lem3468390 _89991 _90000 x f x'') (@lem3468182 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468403 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x' : _89991) : (term514 _89991 s t x') = (term514 _89991 s t x').
Proof. exact (eq_refl (term514 _89991 s t x')). Qed.
Lemma lem3468404 {_89991 : Type'} (s : type686 _89991) (x' : _89991) : (term515 _89991 s x') = (term515 _89991 s x').
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468403 _89991 s t x')). Qed.
Lemma lem3468405 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468407 {_89991 : Type'} (s : type686 _89991) (x' : _89991) : (term516 _89991 s x') = (term516 _89991 s x').
Proof. exact (MK_COMB (@lem3468405 _89991) (@lem3468404 _89991 s x')). Qed.
Lemma lem3468408 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term516 _89991 s x'.
Proof. exact (EQ_MP (@lem3468407 _89991 s x') (@lem3468184 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468414 {A : Type'} (P : A -> Prop) (Q : Prop) : (term539 A P Q) = (term540 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3468415 {_89991 : Type'} (P : type686 _89991) (Q : Prop) : (term541 _89991 P Q) = (term542 _89991 P Q).
Proof. exact (@lem3468414 (_89991 -> Prop) P Q). Qed.
Lemma lem3468416 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term543 _89991 _90000 s x f y) = (term544 _89991 _90000 s x f y).
Proof. exact (@lem3468415 _89991 (term527 _89991 s y) (term525 _89991 _90000 x f y)). Qed.
Lemma lem3468417 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term545 _89991 s y t) = (term526 _89991 s t y).
Proof. exact (eq_refl (term545 _89991 s y t)). Qed.
Lemma lem3468418 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term546 _89991 s y) = (term527 _89991 s y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468417 _89991 s t y)). Qed.
Lemma lem3468419 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468420 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term547 _89991 s y) = (term528 _89991 s y).
Proof. exact (MK_COMB (@lem3468419 _89991) (@lem3468418 _89991 s y)). Qed.
Lemma lem3468421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468422 {_89991 : Type'} (s : type686 _89991) (y : _89991) : (term548 _89991 s y) = (term529 _89991 s y).
Proof. exact (MK_COMB (@lem3468421) (@lem3468420 _89991 s y)). Qed.
Lemma lem3468423 {_89991 _90000 : Type'} (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term525 _89991 _90000 x f y) = (term525 _89991 _90000 x f y).
Proof. exact (eq_refl (term525 _89991 _90000 x f y)). Qed.
Lemma lem3468424 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term543 _89991 _90000 s x f y) = (term530 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468422 _89991 s y) (@lem3468423 _89991 _90000 x f y)). Qed.
Lemma lem3468425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3468426 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term549 _89991 _90000 s x f y) = (term550 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468425) (@lem3468424 _89991 _90000 s x f y)). Qed.
Lemma lem3468427 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term545 _89991 s y t) = (term526 _89991 s t y).
Proof. exact (eq_refl (term545 _89991 s y t)). Qed.
Lemma lem3468428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468429 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (y : _89991) : (term551 _89991 s y t) = (term552 _89991 s t y).
Proof. exact (MK_COMB (@lem3468428) (@lem3468427 _89991 s t y)). Qed.
Lemma lem3468430 {_89991 _90000 : Type'} (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term525 _89991 _90000 x f y) = (term525 _89991 _90000 x f y).
Proof. exact (eq_refl (term525 _89991 _90000 x f y)). Qed.
Lemma lem3468431 {_89991 _90000 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term553 _89991 _90000 s t x f y) = (term554 _89991 _90000 s t x f y).
Proof. exact (MK_COMB (@lem3468429 _89991 s t y) (@lem3468430 _89991 _90000 x f y)). Qed.
Lemma lem3468432 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term555 _89991 _90000 s x f y) = (term556 _89991 _90000 s x f y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468431 _89991 _90000 s t x f y)). Qed.
Lemma lem3468433 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468434 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term544 _89991 _90000 s x f y) = (term557 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468433 _89991) (@lem3468432 _89991 _90000 s x f y)). Qed.
Lemma lem3468435 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : ((term543 _89991 _90000 s x f y) = (term544 _89991 _90000 s x f y)) = ((term530 _89991 _90000 s x f y) = (term557 _89991 _90000 s x f y)).
Proof. exact (MK_COMB (@lem3468426 _89991 _90000 s x f y) (@lem3468434 _89991 _90000 s x f y)). Qed.
Lemma lem3468436 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term530 _89991 _90000 s x f y) = (term557 _89991 _90000 s x f y).
Proof. exact (EQ_MP (@lem3468435 _89991 _90000 s x f y) (@lem3468416 _89991 _90000 s x f y)). Qed.
Lemma lem3468437 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term529 _89991 s x) = (term529 _89991 s x).
Proof. exact (eq_refl (term529 _89991 s x)). Qed.
Lemma lem3468438 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term531 _89991 _90000 s x f y) = (term558 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468437 _89991 s x) (@lem3468436 _89991 _90000 s x f y)). Qed.
Lemma lem3468440 {A : Type'} (P : A -> Prop) (Q : Prop) : (term539 A P Q) = (term540 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3468441 {_89991 : Type'} (P : type686 _89991) (Q : Prop) : (term541 _89991 P Q) = (term542 _89991 P Q).
Proof. exact (@lem3468440 (_89991 -> Prop) P Q). Qed.
Lemma lem3468442 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term559 _89991 _90000 s x f y) = (term560 _89991 _90000 s x f y).
Proof. exact (@lem3468441 _89991 (term527 _89991 s x) (term557 _89991 _90000 s x f y)). Qed.
Lemma lem3468443 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term545 _89991 s x t) = (term526 _89991 s t x).
Proof. exact (eq_refl (term545 _89991 s x t)). Qed.
Lemma lem3468444 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term546 _89991 s x) = (term527 _89991 s x).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468443 _89991 s t x)). Qed.
Lemma lem3468445 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468446 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term547 _89991 s x) = (term528 _89991 s x).
Proof. exact (MK_COMB (@lem3468445 _89991) (@lem3468444 _89991 s x)). Qed.
Lemma lem3468447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468448 {_89991 : Type'} (s : type686 _89991) (x : _89991) : (term548 _89991 s x) = (term529 _89991 s x).
Proof. exact (MK_COMB (@lem3468447) (@lem3468446 _89991 s x)). Qed.
Lemma lem3468449 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term557 _89991 _90000 s x f y) = (term557 _89991 _90000 s x f y).
Proof. exact (eq_refl (term557 _89991 _90000 s x f y)). Qed.
Lemma lem3468450 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term559 _89991 _90000 s x f y) = (term558 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468448 _89991 s x) (@lem3468449 _89991 _90000 s x f y)). Qed.
Lemma lem3468451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3468452 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term561 _89991 _90000 s x f y) = (term562 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468451) (@lem3468450 _89991 _90000 s x f y)). Qed.
Lemma lem3468453 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term545 _89991 s x t) = (term526 _89991 s t x).
Proof. exact (eq_refl (term545 _89991 s x t)). Qed.
Lemma lem3468454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468455 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term551 _89991 s x t) = (term552 _89991 s t x).
Proof. exact (MK_COMB (@lem3468454) (@lem3468453 _89991 s t x)). Qed.
Lemma lem3468456 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term557 _89991 _90000 s x f y) = (term557 _89991 _90000 s x f y).
Proof. exact (eq_refl (term557 _89991 _90000 s x f y)). Qed.
Lemma lem3468457 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term563 _89991 _90000 t s x f y) = (term564 _89991 _90000 t s x f y).
Proof. exact (MK_COMB (@lem3468455 _89991 s t x) (@lem3468456 _89991 _90000 s x f y)). Qed.
Lemma lem3468458 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term565 _89991 _90000 s x f y) = (term566 _89991 _90000 s x f y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468457 _89991 _90000 t s x f y)). Qed.
Lemma lem3468459 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468460 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term560 _89991 _90000 s x f y) = (term567 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468459 _89991) (@lem3468458 _89991 _90000 s x f y)). Qed.
Lemma lem3468461 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : ((term559 _89991 _90000 s x f y) = (term560 _89991 _90000 s x f y)) = ((term558 _89991 _90000 s x f y) = (term567 _89991 _90000 s x f y)).
Proof. exact (MK_COMB (@lem3468452 _89991 _90000 s x f y) (@lem3468460 _89991 _90000 s x f y)). Qed.
Lemma lem3468462 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term558 _89991 _90000 s x f y) = (term567 _89991 _90000 s x f y).
Proof. exact (EQ_MP (@lem3468461 _89991 _90000 s x f y) (@lem3468442 _89991 _90000 s x f y)). Qed.
Lemma lem3468464 {A : Type'} (P : Prop) (Q : A -> Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3468465 {_89991 : Type'} (P : Prop) (Q : type686 _89991) : (term570 _89991 P Q) = (term571 _89991 P Q).
Proof. exact (@lem3468464 (_89991 -> Prop) P Q). Qed.
Lemma lem3468466 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term572 _89991 _90000 t s x f y) = (term573 _89991 _90000 t s x f y).
Proof. exact (@lem3468465 _89991 (term526 _89991 s t x) (term556 _89991 _90000 s x f y)). Qed.
Lemma lem3468467 {_89991 _90000 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term574 _89991 _90000 s x f y t) = (term554 _89991 _90000 s t x f y).
Proof. exact (eq_refl (term574 _89991 _90000 s x f y t)). Qed.
Lemma lem3468468 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term575 _89991 _90000 s x f y) = (term556 _89991 _90000 s x f y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468467 _89991 _90000 s t x f y)). Qed.
Lemma lem3468469 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468470 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term576 _89991 _90000 s x f y) = (term557 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468469 _89991) (@lem3468468 _89991 _90000 s x f y)). Qed.
Lemma lem3468471 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term552 _89991 s t x) = (term552 _89991 s t x).
Proof. exact (eq_refl (term552 _89991 s t x)). Qed.
Lemma lem3468472 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term572 _89991 _90000 t s x f y) = (term564 _89991 _90000 t s x f y).
Proof. exact (MK_COMB (@lem3468471 _89991 s t x) (@lem3468470 _89991 _90000 s x f y)). Qed.
Lemma lem3468473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3468474 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term577 _89991 _90000 t s x f y) = (term578 _89991 _90000 t s x f y).
Proof. exact (MK_COMB (@lem3468473) (@lem3468472 _89991 _90000 t s x f y)). Qed.
Lemma lem3468475 {_89991 _90000 : Type'} (s : type686 _89991) (t' : _89991 -> Prop) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term574 _89991 _90000 s x f y t') = (term554 _89991 _90000 s t' x f y).
Proof. exact (eq_refl (term574 _89991 _90000 s x f y t')). Qed.
Lemma lem3468476 {_89991 : Type'} (s : type686 _89991) (t : _89991 -> Prop) (x : _89991) : (term552 _89991 s t x) = (term552 _89991 s t x).
Proof. exact (eq_refl (term552 _89991 s t x)). Qed.
Lemma lem3468477 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (t' : _89991 -> Prop) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term579 _89991 _90000 t s x f y t') = (term580 _89991 _90000 t s t' x f y).
Proof. exact (MK_COMB (@lem3468476 _89991 s t x) (@lem3468475 _89991 _90000 s t' x f y)). Qed.
Lemma lem3468478 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term581 _89991 _90000 t s x f y) = (term582 _89991 _90000 t s x f y).
Proof. exact (fun_ext (fun t' : _89991 -> Prop => @lem3468477 _89991 _90000 t s t' x f y)). Qed.
Lemma lem3468479 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468480 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term573 _89991 _90000 t s x f y) = (term583 _89991 _90000 t s x f y).
Proof. exact (MK_COMB (@lem3468479 _89991) (@lem3468478 _89991 _90000 t s x f y)). Qed.
Lemma lem3468481 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : ((term572 _89991 _90000 t s x f y) = (term573 _89991 _90000 t s x f y)) = ((term564 _89991 _90000 t s x f y) = (term583 _89991 _90000 t s x f y)).
Proof. exact (MK_COMB (@lem3468474 _89991 _90000 t s x f y) (@lem3468480 _89991 _90000 t s x f y)). Qed.
Lemma lem3468482 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term564 _89991 _90000 t s x f y) = (term583 _89991 _90000 t s x f y).
Proof. exact (EQ_MP (@lem3468481 _89991 _90000 t s x f y) (@lem3468466 _89991 _90000 t s x f y)). Qed.
Lemma lem3468483 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term566 _89991 _90000 s x f y) = (term584 _89991 _90000 s x f y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468482 _89991 _90000 t s x f y)). Qed.
Lemma lem3468484 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468485 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term567 _89991 _90000 s x f y) = (term585 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468484 _89991) (@lem3468483 _89991 _90000 s x f y)). Qed.
Lemma lem3468486 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term558 _89991 _90000 s x f y) = (term585 _89991 _90000 s x f y).
Proof. exact (TRANS (@lem3468462 _89991 _90000 s x f y) (@lem3468485 _89991 _90000 s x f y)). Qed.
Lemma lem3468487 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term531 _89991 _90000 s x f y) = (term585 _89991 _90000 s x f y).
Proof. exact (TRANS (@lem3468438 _89991 _90000 s x f y) (@lem3468486 _89991 _90000 s x f y)). Qed.
Lemma lem3468488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468489 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term532 _89991 _90000 s x f y) = (term586 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468488) (@lem3468487 _89991 _90000 s x f y)). Qed.
Lemma lem3468490 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3468491 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term533 _89991 _90000 s f x y) = (term587 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3468489 _89991 _90000 s x f y) (@lem3468490 _89991 x y)). Qed.
Lemma lem3468493 {A : Type'} (P : A -> Prop) (Q : Prop) : (term539 A P Q) = (term540 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3468494 {_89991 : Type'} (P : type686 _89991) (Q : Prop) : (term541 _89991 P Q) = (term542 _89991 P Q).
Proof. exact (@lem3468493 (_89991 -> Prop) P Q). Qed.
Lemma lem3468495 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term588 _89991 _90000 s f x y) = (term589 _89991 _90000 s f x y).
Proof. exact (@lem3468494 _89991 (term584 _89991 _90000 s x f y) (x = y)). Qed.
Lemma lem3468496 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term590 _89991 _90000 s x f y t) = (term583 _89991 _90000 t s x f y).
Proof. exact (eq_refl (term590 _89991 _90000 s x f y t)). Qed.
Lemma lem3468497 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term591 _89991 _90000 s x f y) = (term584 _89991 _90000 s x f y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468496 _89991 _90000 t s x f y)). Qed.
Lemma lem3468498 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468499 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term592 _89991 _90000 s x f y) = (term585 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468498 _89991) (@lem3468497 _89991 _90000 s x f y)). Qed.
Lemma lem3468500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468501 {_89991 _90000 : Type'} (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term593 _89991 _90000 s x f y) = (term586 _89991 _90000 s x f y).
Proof. exact (MK_COMB (@lem3468500) (@lem3468499 _89991 _90000 s x f y)). Qed.
Lemma lem3468502 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3468503 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term588 _89991 _90000 s f x y) = (term587 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3468501 _89991 _90000 s x f y) (@lem3468502 _89991 x y)). Qed.
Lemma lem3468504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3468505 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term594 _89991 _90000 s f x y) = (term595 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3468504) (@lem3468503 _89991 _90000 s f x y)). Qed.
Lemma lem3468506 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term590 _89991 _90000 s x f y t) = (term583 _89991 _90000 t s x f y).
Proof. exact (eq_refl (term590 _89991 _90000 s x f y t)). Qed.
Lemma lem3468507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468508 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term596 _89991 _90000 s x f y t) = (term597 _89991 _90000 t s x f y).
Proof. exact (MK_COMB (@lem3468507) (@lem3468506 _89991 _90000 t s x f y)). Qed.
Lemma lem3468509 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3468510 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term598 _89991 _90000 s f t x y) = (term599 _89991 _90000 t s f x y).
Proof. exact (MK_COMB (@lem3468508 _89991 _90000 t s x f y) (@lem3468509 _89991 x y)). Qed.
Lemma lem3468511 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term600 _89991 _90000 s f x y) = (term601 _89991 _90000 s f x y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468510 _89991 _90000 t s f x y)). Qed.
Lemma lem3468512 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468513 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term589 _89991 _90000 s f x y) = (term602 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3468512 _89991) (@lem3468511 _89991 _90000 s f x y)). Qed.
Lemma lem3468514 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : ((term588 _89991 _90000 s f x y) = (term589 _89991 _90000 s f x y)) = ((term587 _89991 _90000 s f x y) = (term602 _89991 _90000 s f x y)).
Proof. exact (MK_COMB (@lem3468505 _89991 _90000 s f x y) (@lem3468513 _89991 _90000 s f x y)). Qed.
Lemma lem3468515 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term587 _89991 _90000 s f x y) = (term602 _89991 _90000 s f x y).
Proof. exact (EQ_MP (@lem3468514 _89991 _90000 s f x y) (@lem3468495 _89991 _90000 s f x y)). Qed.
Lemma lem3468517 {A : Type'} (P : A -> Prop) (Q : Prop) : (term539 A P Q) = (term540 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3468518 {_89991 : Type'} (P : type686 _89991) (Q : Prop) : (term541 _89991 P Q) = (term542 _89991 P Q).
Proof. exact (@lem3468517 (_89991 -> Prop) P Q). Qed.
Lemma lem3468519 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term603 _89991 _90000 t s f x y) = (term604 _89991 _90000 t s f x y).
Proof. exact (@lem3468518 _89991 (term582 _89991 _90000 t s x f y) (x = y)). Qed.
Lemma lem3468520 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (t' : _89991 -> Prop) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term605 _89991 _90000 t s x f y t') = (term580 _89991 _90000 t s t' x f y).
Proof. exact (eq_refl (term605 _89991 _90000 t s x f y t')). Qed.
Lemma lem3468521 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term606 _89991 _90000 t s x f y) = (term582 _89991 _90000 t s x f y).
Proof. exact (fun_ext (fun t' : _89991 -> Prop => @lem3468520 _89991 _90000 t s t' x f y)). Qed.
Lemma lem3468522 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468523 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term607 _89991 _90000 t s x f y) = (term583 _89991 _90000 t s x f y).
Proof. exact (MK_COMB (@lem3468522 _89991) (@lem3468521 _89991 _90000 t s x f y)). Qed.
Lemma lem3468524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468525 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term608 _89991 _90000 t s x f y) = (term597 _89991 _90000 t s x f y).
Proof. exact (MK_COMB (@lem3468524) (@lem3468523 _89991 _90000 t s x f y)). Qed.
Lemma lem3468526 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3468527 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term603 _89991 _90000 t s f x y) = (term599 _89991 _90000 t s f x y).
Proof. exact (MK_COMB (@lem3468525 _89991 _90000 t s x f y) (@lem3468526 _89991 x y)). Qed.
Lemma lem3468528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3468529 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term609 _89991 _90000 t s f x y) = (term610 _89991 _90000 t s f x y).
Proof. exact (MK_COMB (@lem3468528) (@lem3468527 _89991 _90000 t s f x y)). Qed.
Lemma lem3468530 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (t' : _89991 -> Prop) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term605 _89991 _90000 t s x f y t') = (term580 _89991 _90000 t s t' x f y).
Proof. exact (eq_refl (term605 _89991 _90000 t s x f y t')). Qed.
Lemma lem3468531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3468532 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (t' : _89991 -> Prop) (x : _89991) (f : _89991 -> _90000) (y : _89991) : (term611 _89991 _90000 t s x f y t') = (term612 _89991 _90000 t s t' x f y).
Proof. exact (MK_COMB (@lem3468531) (@lem3468530 _89991 _90000 t s t' x f y)). Qed.
Lemma lem3468533 {_89991 : Type'} (x : _89991) (y : _89991) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3468534 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (t' : _89991 -> Prop) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term613 _89991 _90000 t s f t' x y) = (term614 _89991 _90000 t s t' f x y).
Proof. exact (MK_COMB (@lem3468532 _89991 _90000 t s t' x f y) (@lem3468533 _89991 x y)). Qed.
Lemma lem3468535 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term615 _89991 _90000 t s f x y) = (term616 _89991 _90000 t s f x y).
Proof. exact (fun_ext (fun t' : _89991 -> Prop => @lem3468534 _89991 _90000 t s t' f x y)). Qed.
Lemma lem3468536 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468537 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term604 _89991 _90000 t s f x y) = (term617 _89991 _90000 t s f x y).
Proof. exact (MK_COMB (@lem3468536 _89991) (@lem3468535 _89991 _90000 t s f x y)). Qed.
Lemma lem3468538 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : ((term603 _89991 _90000 t s f x y) = (term604 _89991 _90000 t s f x y)) = ((term599 _89991 _90000 t s f x y) = (term617 _89991 _90000 t s f x y)).
Proof. exact (MK_COMB (@lem3468529 _89991 _90000 t s f x y) (@lem3468537 _89991 _90000 t s f x y)). Qed.
Lemma lem3468539 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term599 _89991 _90000 t s f x y) = (term617 _89991 _90000 t s f x y).
Proof. exact (EQ_MP (@lem3468538 _89991 _90000 t s f x y) (@lem3468519 _89991 _90000 t s f x y)). Qed.
Lemma lem3468540 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term601 _89991 _90000 s f x y) = (term618 _89991 _90000 s f x y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468539 _89991 _90000 t s f x y)). Qed.
Lemma lem3468541 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468542 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term602 _89991 _90000 s f x y) = (term619 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3468541 _89991) (@lem3468540 _89991 _90000 s f x y)). Qed.
Lemma lem3468543 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term587 _89991 _90000 s f x y) = (term619 _89991 _90000 s f x y).
Proof. exact (TRANS (@lem3468515 _89991 _90000 s f x y) (@lem3468542 _89991 _90000 s f x y)). Qed.
Lemma lem3468544 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term533 _89991 _90000 s f x y) = (term619 _89991 _90000 s f x y).
Proof. exact (TRANS (@lem3468491 _89991 _90000 s f x y) (@lem3468543 _89991 _90000 s f x y)). Qed.
Lemma lem3468545 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term534 _89991 _90000 s f x) = (term620 _89991 _90000 s f x).
Proof. exact (fun_ext (fun y : _89991 => @lem3468544 _89991 _90000 s f x y)). Qed.
Lemma lem3468546 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468547 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term535 _89991 _90000 s f x) = (term621 _89991 _90000 s f x).
Proof. exact (MK_COMB (@lem3468546 _89991) (@lem3468545 _89991 _90000 s f x)). Qed.
Lemma lem3468548 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term536 _89991 _90000 s f) = (term622 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _89991 => @lem3468547 _89991 _90000 s f x)). Qed.
Lemma lem3468549 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468550 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term537 _89991 _90000 s f) = (term623 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3468549 _89991) (@lem3468548 _89991 _90000 s f)). Qed.
Lemma lem3468581 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (t' : _89991 -> Prop) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term614 _89991 _90000 t s t' f x y) = (term614 _89991 _90000 t s t' f x y).
Proof. exact (eq_refl (term614 _89991 _90000 t s t' f x y)). Qed.
Lemma lem3468582 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term616 _89991 _90000 t s f x y) = (term616 _89991 _90000 t s f x y).
Proof. exact (fun_ext (fun t' : _89991 -> Prop => @lem3468581 _89991 _90000 t s t' f x y)). Qed.
Lemma lem3468583 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468584 {_89991 _90000 : Type'} (t : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term617 _89991 _90000 t s f x y) = (term617 _89991 _90000 t s f x y).
Proof. exact (MK_COMB (@lem3468583 _89991) (@lem3468582 _89991 _90000 t s f x y)). Qed.
Lemma lem3468585 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term618 _89991 _90000 s f x y) = (term618 _89991 _90000 s f x y).
Proof. exact (fun_ext (fun t : _89991 -> Prop => @lem3468584 _89991 _90000 t s f x y)). Qed.
Lemma lem3468586 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468587 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) (y : _89991) : (term619 _89991 _90000 s f x y) = (term619 _89991 _90000 s f x y).
Proof. exact (MK_COMB (@lem3468586 _89991) (@lem3468585 _89991 _90000 s f x y)). Qed.
Lemma lem3468588 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term620 _89991 _90000 s f x) = (term620 _89991 _90000 s f x).
Proof. exact (fun_ext (fun y : _89991 => @lem3468587 _89991 _90000 s f x y)). Qed.
Lemma lem3468589 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468590 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (x : _89991) : (term621 _89991 _90000 s f x) = (term621 _89991 _90000 s f x).
Proof. exact (MK_COMB (@lem3468589 _89991) (@lem3468588 _89991 _90000 s f x)). Qed.
Lemma lem3468591 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term622 _89991 _90000 s f) = (term622 _89991 _90000 s f).
Proof. exact (fun_ext (fun x : _89991 => @lem3468590 _89991 _90000 s f x)). Qed.
Lemma lem3468592 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468593 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term623 _89991 _90000 s f) = (term623 _89991 _90000 s f).
Proof. exact (MK_COMB (@lem3468592 _89991) (@lem3468591 _89991 _90000 s f)). Qed.
Lemma lem3468594 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : (term537 _89991 _90000 s f) = (term623 _89991 _90000 s f).
Proof. exact (TRANS (@lem3468550 _89991 _90000 s f) (@lem3468593 _89991 _90000 s f)). Qed.
Lemma lem3468595 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term623 _89991 _90000 s f.
Proof. exact (EQ_MP (@lem3468594 _89991 _90000 s f) (@lem3468176 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3468613 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) (x' : _89991) : (term502 _89991 _90000 x f s t x') = (term624 _89991 _90000 s x f t x').
Proof. exact (@lem19490 (term495 _89991 s t x') (term500 _89991 _90000 x f x') (term492 _89991 t x')). Qed.
Lemma lem3468614 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) : (term503 _89991 _90000 x f s t) = (term625 _89991 _90000 s x f t).
Proof. exact (fun_ext (fun x' : _89991 => @lem3468613 _89991 _90000 s x f t x')). Qed.
Lemma lem3468615 {_89991 : Type'} : (@all _89991) = (@all _89991).
Proof. exact (eq_refl (@all _89991)). Qed.
Lemma lem3468617 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) : (term504 _89991 _90000 x f s t) = (term626 _89991 _90000 s x f t).
Proof. exact (MK_COMB (@lem3468615 _89991) (@lem3468614 _89991 _90000 s x f t)). Qed.
Lemma lem3468618 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term626 _89991 _90000 s x f t.
Proof. exact (EQ_MP (@lem3468617 _89991 _90000 s x f t) (@lem3468187 _89991 _90000 t s x f x''' h1)). Qed.
Lemma lem3468636 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x''' : type684 _89991) (x' : _89991 -> Prop) : (term487 _89991 _90000 s x f x''' x') = (term627 _89991 _90000 x f s x''' x').
Proof. exact (@lem19490 (x = (term480 _89991 _90000 f x''' x')) (term485 _89991 s x') (term477 _89991 x''' x')). Qed.
Lemma lem3468637 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x''' : type684 _89991) : (term488 _89991 _90000 s x f x''') = (term628 _89991 _90000 x f s x''').
Proof. exact (fun_ext (fun x' : _89991 -> Prop => @lem3468636 _89991 _90000 x f s x''' x')). Qed.
Lemma lem3468638 {_89991 : Type'} : (@all (_89991 -> Prop)) = (@all (_89991 -> Prop)).
Proof. exact (eq_refl (@all (_89991 -> Prop))). Qed.
Lemma lem3468640 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x''' : type684 _89991) : (term489 _89991 _90000 s x f x''') = (term629 _89991 _90000 x f s x''').
Proof. exact (MK_COMB (@lem3468638 _89991) (@lem3468637 _89991 _90000 x f s x''')). Qed.
Lemma lem3468641 {_89991 _90000 : Type'} (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term629 _89991 _90000 x f s x'''.
Proof. exact (EQ_MP (@lem3468640 _89991 _90000 x f s x''') (@lem3468186 _89991 _90000 t s x f x''' h1)). Qed.
Lemma lem3468654 {_89991 _90000 : Type'} (_36617 : _89991) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term630 _89991 _90000 x f x'' _36617.
Proof. exact (@lem3468391 _89991 _90000 x' s x f x'' h1 _36617). Qed.
Lemma lem3468655 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term630 _89991 _90000 x f x'' _36617) = (term509 _89991 _90000 x f x'' _36617).
Proof. exact (eq_refl (term630 _89991 _90000 x f x'' _36617)). Qed.
Lemma lem3468657 {_89991 _90000 : Type'} (_36618 : _89991 -> Prop) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term631 _89991 s x' _36618.
Proof. exact (@lem3468408 _89991 _90000 x' s x f x'' h1 _36618). Qed.
Lemma lem3468658 {_89991 : Type'} (s : type686 _89991) (_36618 : _89991 -> Prop) (x' : _89991) : (term631 _89991 s x' _36618) = (term514 _89991 s _36618 x').
Proof. exact (eq_refl (term631 _89991 s x' _36618)). Qed.
Lemma lem3468660 {_89991 _90000 : Type'} (_36619 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term632 _89991 _90000 s f _36619.
Proof. exact (@lem3468595 _89991 _90000 x'''' s f h1 _36619). Qed.
Lemma lem3468661 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (_36619 : _89991) : (term632 _89991 _90000 s f _36619) = (term621 _89991 _90000 s f _36619).
Proof. exact (eq_refl (term632 _89991 _90000 s f _36619)). Qed.
Lemma lem3468662 {_89991 _90000 : Type'} (_36619 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term621 _89991 _90000 s f _36619.
Proof. exact (EQ_MP (@lem3468661 _89991 _90000 s f _36619) (@lem3468660 _89991 _90000 _36619 x'''' s f h1)). Qed.
Lemma lem3468663 {_89991 _90000 : Type'} (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term633 _89991 _90000 s f _36619 _36620.
Proof. exact (@lem3468662 _89991 _90000 _36619 x'''' s f h1 _36620). Qed.
Lemma lem3468664 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term633 _89991 _90000 s f _36619 _36620) = (term619 _89991 _90000 s f _36619 _36620).
Proof. exact (eq_refl (term633 _89991 _90000 s f _36619 _36620)). Qed.
Lemma lem3468665 {_89991 _90000 : Type'} (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term619 _89991 _90000 s f _36619 _36620.
Proof. exact (EQ_MP (@lem3468664 _89991 _90000 s f _36619 _36620) (@lem3468663 _89991 _90000 _36619 _36620 x'''' s f h1)). Qed.
Lemma lem3468666 {_89991 _90000 : Type'} (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term634 _89991 _90000 s f _36619 _36620 _36621.
Proof. exact (@lem3468665 _89991 _90000 _36619 _36620 x'''' s f h1 _36621). Qed.
Lemma lem3468667 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term634 _89991 _90000 s f _36619 _36620 _36621) = (term617 _89991 _90000 _36621 s f _36619 _36620).
Proof. exact (eq_refl (term634 _89991 _90000 s f _36619 _36620 _36621)). Qed.
Lemma lem3468668 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term617 _89991 _90000 _36621 s f _36619 _36620.
Proof. exact (EQ_MP (@lem3468667 _89991 _90000 _36621 s f _36619 _36620) (@lem3468666 _89991 _90000 _36619 _36620 _36621 x'''' s f h1)). Qed.
Lemma lem3468669 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) (_36622 : _89991 -> Prop) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term635 _89991 _90000 _36621 s f _36619 _36620 _36622.
Proof. exact (@lem3468668 _89991 _90000 _36621 _36619 _36620 x'''' s f h1 _36622). Qed.
Lemma lem3468670 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term635 _89991 _90000 _36621 s f _36619 _36620 _36622) = (term614 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (eq_refl (term635 _89991 _90000 _36621 s f _36619 _36620 _36622)). Qed.
Lemma lem3468671 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36622 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term614 _89991 _90000 _36621 s _36622 f _36619 _36620.
Proof. exact (EQ_MP (@lem3468670 _89991 _90000 _36621 s _36622 f _36619 _36620) (@lem3468669 _89991 _90000 _36621 _36619 _36620 _36622 x'''' s f h1)). Qed.
Lemma lem3468672 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term636 _89991 _90000 s x f t _36623.
Proof. exact (@lem3468618 _89991 _90000 t s x f x''' h1 _36623). Qed.
Lemma lem3468673 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) (_36623 : _89991) : (term636 _89991 _90000 s x f t _36623) = (term624 _89991 _90000 s x f t _36623).
Proof. exact (eq_refl (term636 _89991 _90000 s x f t _36623)). Qed.
Lemma lem3468674 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term624 _89991 _90000 s x f t _36623.
Proof. exact (EQ_MP (@lem3468673 _89991 _90000 s x f t _36623) (@lem3468672 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3468675 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term637 _89991 _90000 x f s x''' _36624.
Proof. exact (@lem3468641 _89991 _90000 t s x f x''' h1 _36624). Qed.
Lemma lem3468676 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term637 _89991 _90000 x f s x''' _36624) = (term627 _89991 _90000 x f s x''' _36624).
Proof. exact (eq_refl (term637 _89991 _90000 x f s x''' _36624)). Qed.
Lemma lem3468677 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term627 _89991 _90000 x f s x''' _36624.
Proof. exact (EQ_MP (@lem3468676 _89991 _90000 x f s x''' _36624) (@lem3468675 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3468721 {_89991 _90000 : Type'} (_36617 : _89991) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term509 _89991 _90000 x f x'' _36617.
Proof. exact (EQ_MP (@lem3468655 _89991 _90000 x f x'' _36617) (@lem3468654 _89991 _90000 _36617 x' s x f x'' h1)). Qed.
Lemma lem3468723 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : x = (@I (_89991 -> _90000) f x').
Proof. exact (proj1 (@lem3468181 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468735 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term614 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term638 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (@lem3465963 (term526 _89991 s _36621 _36619) (term554 _89991 _90000 s _36622 _36619 f _36620) (_36619 = _36620)). Qed.
Lemma lem3468736 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term639 _89991 _90000 s _36622 f _36619 _36620) = (term640 _89991 _90000 s _36622 f _36619 _36620).
Proof. exact (@lem3465963 (term526 _89991 s _36622 _36620) (term525 _89991 _90000 _36619 f _36620) (_36619 = _36620)). Qed.
Lemma lem3468747 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term640 _89991 _90000 s _36622 f _36619 _36620) = (term641 _89991 _90000 s _36622 f _36619 _36620).
Proof. exact (@lem3465963 (term485 _89991 s _36622) (term508 _89991 _36622 _36620) (term642 _89991 _90000 f _36619 _36620)). Qed.
Lemma lem3468748 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term639 _89991 _90000 s _36622 f _36619 _36620) = (term641 _89991 _90000 s _36622 f _36619 _36620).
Proof. exact (TRANS (@lem3468736 _89991 _90000 s _36622 f _36619 _36620) (@lem3468747 _89991 _90000 s _36622 f _36619 _36620)). Qed.
Lemma lem3468749 {_89991 : Type'} (s : type686 _89991) (_36621 : _89991 -> Prop) (_36619 : _89991) : (term552 _89991 s _36621 _36619) = (term552 _89991 s _36621 _36619).
Proof. exact (eq_refl (term552 _89991 s _36621 _36619)). Qed.
Lemma lem3468750 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term638 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term643 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (MK_COMB (@lem3468749 _89991 s _36621 _36619) (@lem3468748 _89991 _90000 s _36622 f _36619 _36620)). Qed.
Lemma lem3468757 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term643 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term644 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (@lem3465963 (term485 _89991 s _36621) (term508 _89991 _36621 _36619) (term641 _89991 _90000 s _36622 f _36619 _36620)). Qed.
Lemma lem3468758 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term638 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term644 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (TRANS (@lem3468750 _89991 _90000 _36621 s _36622 f _36619 _36620) (@lem3468757 _89991 _90000 _36621 s _36622 f _36619 _36620)). Qed.
Lemma lem3468760 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term614 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term644 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (TRANS (@lem3468735 _89991 _90000 _36621 s _36622 f _36619 _36620) (@lem3468758 _89991 _90000 _36621 s _36622 f _36619 _36620)). Qed.
Lemma lem3468761 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36622 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term644 _89991 _90000 _36621 s _36622 f _36619 _36620.
Proof. exact (EQ_MP (@lem3468760 _89991 _90000 _36621 s _36622 f _36619 _36620) (@lem3468671 _89991 _90000 _36621 _36622 _36619 _36620 x'''' s f h1)). Qed.
Lemma lem3468767 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term645 _89991 _90000 s x f x''' _36624.
Proof. exact (proj1 (@lem3468677 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3468773 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term646 _89991 s x''' _36624.
Proof. exact (proj2 (@lem3468677 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3468779 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term647 _89991 _90000 x f s t _36623.
Proof. exact (proj1 (@lem3468674 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3468785 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term648 _89991 _90000 x f t _36623.
Proof. exact (proj2 (@lem3468674 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3468842 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term649 _89991 _90000 f x'' _36617) = (term649 _89991 _90000 f x'' _36617).
Proof. exact (eq_refl (term649 _89991 _90000 f x'' _36617)). Qed.
Lemma lem3468843 {_89991 _90000 : Type'} (_36617 : _89991) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : (term650 _89991 _90000 f x'' _36617 x) = (term651 _89991 _90000 x'' _36617 f x').
Proof. exact (MK_COMB (@lem3468842 _89991 _90000 f x'' _36617) (@lem3468723 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468844 {_89991 _90000 : Type'} (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term651 _89991 _90000 x'' _36617 f x') = (term652 _89991 _90000 x' f x'' _36617).
Proof. exact (eq_refl (term651 _89991 _90000 x'' _36617 f x')). Qed.
Lemma lem3468845 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) (x : _90000) : (term653 _89991 _90000 f x'' _36617 x) = (term653 _89991 _90000 f x'' _36617 x).
Proof. exact (eq_refl (term653 _89991 _90000 f x'' _36617 x)). Qed.
Lemma lem3468846 {_89991 _90000 : Type'} (x : _90000) (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : ((term650 _89991 _90000 f x'' _36617 x) = (term651 _89991 _90000 x'' _36617 f x')) = ((term650 _89991 _90000 f x'' _36617 x) = (term652 _89991 _90000 x' f x'' _36617)).
Proof. exact (MK_COMB (@lem3468845 _89991 _90000 f x'' _36617 x) (@lem3468844 _89991 _90000 x' f x'' _36617)). Qed.
Lemma lem3468847 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term650 _89991 _90000 f x'' _36617 x) = (term509 _89991 _90000 x f x'' _36617).
Proof. exact (eq_refl (term650 _89991 _90000 f x'' _36617 x)). Qed.
Lemma lem3468848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3468849 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term653 _89991 _90000 f x'' _36617 x) = (term654 _89991 _90000 x f x'' _36617).
Proof. exact (MK_COMB (@lem3468848) (@lem3468847 _89991 _90000 x f x'' _36617)). Qed.
Lemma lem3468850 {_89991 _90000 : Type'} (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term652 _89991 _90000 x' f x'' _36617) = (term652 _89991 _90000 x' f x'' _36617).
Proof. exact (eq_refl (term652 _89991 _90000 x' f x'' _36617)). Qed.
Lemma lem3468851 {_89991 _90000 : Type'} (x : _90000) (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : ((term650 _89991 _90000 f x'' _36617 x) = (term652 _89991 _90000 x' f x'' _36617)) = ((term509 _89991 _90000 x f x'' _36617) = (term652 _89991 _90000 x' f x'' _36617)).
Proof. exact (MK_COMB (@lem3468849 _89991 _90000 x f x'' _36617) (@lem3468850 _89991 _90000 x' f x'' _36617)). Qed.
Lemma lem3468852 {_89991 _90000 : Type'} (x : _90000) (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : ((term650 _89991 _90000 f x'' _36617 x) = (term651 _89991 _90000 x'' _36617 f x')) = ((term509 _89991 _90000 x f x'' _36617) = (term652 _89991 _90000 x' f x'' _36617)).
Proof. exact (TRANS (@lem3468846 _89991 _90000 x x' f x'' _36617) (@lem3468851 _89991 _90000 x x' f x'' _36617)). Qed.
Lemma lem3468853 {_89991 _90000 : Type'} (_36617 : _89991) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : (term509 _89991 _90000 x f x'' _36617) = (term652 _89991 _90000 x' f x'' _36617).
Proof. exact (EQ_MP (@lem3468852 _89991 _90000 x x' f x'' _36617) (@lem3468843 _89991 _90000 _36617 x' s x f x'' h1)). Qed.
Lemma lem3468854 {_89991 _90000 : Type'} (_36617 : _89991) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term652 _89991 _90000 x' f x'' _36617.
Proof. exact (EQ_MP (@lem3468853 _89991 _90000 _36617 x' s x f x'' h1) (@lem3468721 _89991 _90000 _36617 x' s x f x'' h1)). Qed.
Lemma lem3468868 {_89991 _90000 : Type'} (_36618 : _89991 -> Prop) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term514 _89991 s _36618 x'.
Proof. exact (EQ_MP (@lem3468658 _89991 s _36618 x') (@lem3468657 _89991 _90000 _36618 x' s x f x'' h1)). Qed.
Lemma lem3468933 {_90000 : Type'} (x : _90000) : x = x.
Proof. exact (@lem21386 _90000 x). Qed.
Lemma lem3468934 {_90000 : Type'} (x : _90000) : x = x.
Proof. exact (@lem3468933 _90000 x). Qed.
Lemma lem3468935 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x' : _89991) : (@I (_89991 -> _90000) f x') = (@I (_89991 -> _90000) f x').
Proof. exact (@lem3468934 _90000 (@I (_89991 -> _90000) f x')). Qed.
Lemma lem3468936 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x' : _89991) : term655 _89991 _90000 f x'.
Proof. exact (fun h0 : term656 _89991 _90000 f x' => @lem3468935 _89991 _90000 f x'). Qed.
Lemma lem3468938 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3468939 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x' : _89991) : (term655 _89991 _90000 f x') = ((@I (_89991 -> _90000) f x') = (@I (_89991 -> _90000) f x')).
Proof. exact (@lem3468938 ((@I (_89991 -> _90000) f x') = (@I (_89991 -> _90000) f x'))). Qed.
Lemma lem3468940 {_89991 _90000 : Type'} (f : _89991 -> _90000) (x' : _89991) : (@I (_89991 -> _90000) f x') = (@I (_89991 -> _90000) f x').
Proof. exact (EQ_MP (@lem3468939 _89991 _90000 f x') (@lem3468936 _89991 _90000 f x')). Qed.
Lemma lem3468942 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : @I ((_89991 -> Prop) -> Prop) s x''.
Proof. exact (proj1 (@lem3468180 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468943 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term658 _89991 s x''.
Proof. exact (fun h0 : term485 _89991 s x'' => @lem3468942 _89991 _90000 x' s x f x'' h1). Qed.
Lemma lem3468945 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3468946 {_89991 : Type'} (s : type686 _89991) (x'' : _89991 -> Prop) : (term658 _89991 s x'') = (@I ((_89991 -> Prop) -> Prop) s x'').
Proof. exact (@lem3468945 (@I ((_89991 -> Prop) -> Prop) s x'')). Qed.
Lemma lem3468947 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : @I ((_89991 -> Prop) -> Prop) s x''.
Proof. exact (EQ_MP (@lem3468946 _89991 s x'') (@lem3468943 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468953 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3468954 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : (term514 _89991 s _36618 x') = (term659 _89991 x' s _36618).
Proof. exact (@lem3468953 (@I (_89991 -> Prop) _36618 x') (term485 _89991 s _36618)). Qed.
Lemma lem3468960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3468961 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : (term660 _89991 s _36618 x') = (term661 _89991 x' s _36618).
Proof. exact (MK_COMB (@lem3468960) (@lem3468954 _89991 x' s _36618)). Qed.
Lemma lem3468967 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : (term659 _89991 x' s _36618) = (term659 _89991 x' s _36618).
Proof. exact (eq_refl (term659 _89991 x' s _36618)). Qed.
Lemma lem3468968 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : ((term514 _89991 s _36618 x') = (term659 _89991 x' s _36618)) = ((term659 _89991 x' s _36618) = (term659 _89991 x' s _36618)).
Proof. exact (MK_COMB (@lem3468961 _89991 x' s _36618) (@lem3468967 _89991 x' s _36618)). Qed.
Lemma lem3468970 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3468971 (x : Prop) : (x = x) = True.
Proof. exact (@lem3468970 Prop x). Qed.
Lemma lem3468972 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : ((term659 _89991 x' s _36618) = (term659 _89991 x' s _36618)) = True.
Proof. exact (@lem3468971 (term659 _89991 x' s _36618)). Qed.
Lemma lem3468973 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : ((term514 _89991 s _36618 x') = (term659 _89991 x' s _36618)) = True.
Proof. exact (TRANS (@lem3468968 _89991 x' s _36618) (@lem3468972 _89991 x' s _36618)). Qed.
Lemma lem3468974 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : True = ((term514 _89991 s _36618 x') = (term659 _89991 x' s _36618)).
Proof. exact (SYM (@lem3468973 _89991 x' s _36618)). Qed.
Lemma lem3468975 {_89991 : Type'} (x' : _89991) (s : type686 _89991) (_36618 : _89991 -> Prop) : (term514 _89991 s _36618 x') = (term659 _89991 x' s _36618).
Proof. exact (EQ_MP (@lem3468974 _89991 x' s _36618) (@lem0)). Qed.
Lemma lem3468976 {_89991 _90000 : Type'} (_36618 : _89991 -> Prop) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term659 _89991 x' s _36618.
Proof. exact (EQ_MP (@lem3468975 _89991 x' s _36618) (@lem3468868 _89991 _90000 _36618 x' s x f x'' h1)). Qed.
Lemma lem3468978 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3468979 {_89991 : Type'} (s : type686 _89991) (_36618 : _89991 -> Prop) (x' : _89991) : (term659 _89991 x' s _36618) = (term663 _89991 s _36618 x').
Proof. exact (@lem3468978 (term485 _89991 s _36618) (@I (_89991 -> Prop) _36618 x')). Qed.
Lemma lem3468981 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3468982 {_89991 : Type'} (s : type686 _89991) (_36618 : _89991 -> Prop) : (term664 _89991 s _36618) = (@I ((_89991 -> Prop) -> Prop) s _36618).
Proof. exact (@lem3468981 (@I ((_89991 -> Prop) -> Prop) s _36618)). Qed.
Lemma lem3468983 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3468984 {_89991 : Type'} (s : type686 _89991) (_36618 : _89991 -> Prop) : (term665 _89991 s _36618) = (term666 _89991 s _36618).
Proof. exact (MK_COMB (@lem3468983) (@lem3468982 _89991 s _36618)). Qed.
Lemma lem3468985 {_89991 : Type'} (_36618 : _89991 -> Prop) (x' : _89991) : (@I (_89991 -> Prop) _36618 x') = (@I (_89991 -> Prop) _36618 x').
Proof. exact (eq_refl (@I (_89991 -> Prop) _36618 x')). Qed.
Lemma lem3468986 {_89991 : Type'} (s : type686 _89991) (_36618 : _89991 -> Prop) (x' : _89991) : (term663 _89991 s _36618 x') = (term667 _89991 s _36618 x').
Proof. exact (MK_COMB (@lem3468984 _89991 s _36618) (@lem3468985 _89991 _36618 x')). Qed.
Lemma lem3468987 {_89991 : Type'} (s : type686 _89991) (_36618 : _89991 -> Prop) (x' : _89991) : (term659 _89991 x' s _36618) = (term667 _89991 s _36618 x').
Proof. exact (TRANS (@lem3468979 _89991 s _36618 x') (@lem3468986 _89991 s _36618 x')). Qed.
Lemma lem3468990 {_89991 _90000 : Type'} (_36618 : _89991 -> Prop) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term667 _89991 s _36618 x'.
Proof. exact (EQ_MP (@lem3468987 _89991 s _36618 x') (@lem3468976 _89991 _90000 _36618 x' s x f x'' h1)). Qed.
Lemma lem3468991 {_89991 _90000 : Type'} (_36618 : _89991 -> Prop) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term667 _89991 s _36618 x'.
Proof. exact (@lem3468990 _89991 _90000 _36618 x' s x f x'' h1). Qed.
Lemma lem3468992 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term667 _89991 s x'' x'.
Proof. exact (@lem3468991 _89991 _90000 x'' x' s x f x'' h1). Qed.
Lemma lem3468995 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : @I (_89991 -> Prop) x'' x'.
Proof. exact (@lem3468992 _89991 _90000 x' s x f x'' h1 (@lem3468947 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3468996 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term668 _89991 x'' x'.
Proof. exact (fun h0 : term508 _89991 x'' x' => @lem3468995 _89991 _90000 x' s x f x'' h1). Qed.
Lemma lem3468998 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3468999 {_89991 : Type'} (x'' : _89991 -> Prop) (x' : _89991) : (term668 _89991 x'' x') = (@I (_89991 -> Prop) x'' x').
Proof. exact (@lem3468998 (@I (_89991 -> Prop) x'' x')). Qed.
Lemma lem3469000 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : @I (_89991 -> Prop) x'' x'.
Proof. exact (EQ_MP (@lem3468999 _89991 x'' x') (@lem3468996 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3469002 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3469003 {_89991 _90000 : Type'} (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term652 _89991 _90000 x' f x'' _36617) = (term671 _89991 _90000 x' f x'' _36617).
Proof. exact (@lem3469002 ((@I (_89991 -> _90000) f x') = (@I (_89991 -> _90000) f _36617)) (@I (_89991 -> Prop) x'' _36617)). Qed.
Lemma lem3469005 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3469006 {_89991 _90000 : Type'} (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term671 _89991 _90000 x' f x'' _36617) = (term672 _89991 _90000 x' f x'' _36617).
Proof. exact (@lem3469005 (term673 _89991 _90000 x' f x'' _36617)). Qed.
Lemma lem3469007 {_89991 _90000 : Type'} (x' : _89991) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (_36617 : _89991) : (term652 _89991 _90000 x' f x'' _36617) = (term672 _89991 _90000 x' f x'' _36617).
Proof. exact (TRANS (@lem3469003 _89991 _90000 x' f x'' _36617) (@lem3469006 _89991 _90000 x' f x'' _36617)). Qed.
Lemma lem3469009 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term674 _89991 _90000 f x'' x'.
Proof. exact (conj (@lem3468940 _89991 _90000 f x') (@lem3469000 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3469011 {_89991 _90000 : Type'} (_36617 : _89991) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term672 _89991 _90000 x' f x'' _36617.
Proof. exact (EQ_MP (@lem3469007 _89991 _90000 x' f x'' _36617) (@lem3468854 _89991 _90000 _36617 x' s x f x'' h1)). Qed.
Lemma lem3469012 {_89991 _90000 : Type'} (_36617 : _89991) (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term672 _89991 _90000 x' f x'' _36617.
Proof. exact (@lem3469011 _89991 _90000 _36617 x' s x f x'' h1). Qed.
Lemma lem3469013 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term675 _89991 _90000 f x'' x'.
Proof. exact (@lem3469012 _89991 _90000 x' x' s x f x'' h1). Qed.
Lemma lem3469016 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : False.
Proof. exact (@lem3469013 _89991 _90000 x' s x f x'' h1 (@lem3469009 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3469017 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : term676.
Proof. exact (fun h0 : ~ False => @lem3469016 _89991 _90000 x' s x f x'' h1). Qed.
Lemma lem3469019 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469020 : term676 = False.
Proof. exact (@lem3469019 False). Qed.
Lemma lem3469022 {_89991 : Type'} : (@I (_89991 -> Prop)) = (@I (_89991 -> Prop)).
Proof. exact (eq_refl (@I (_89991 -> Prop))). Qed.
Lemma lem3469023 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36651 : _89991 -> Prop) (h1 : _36649 = _36651) : _36649 = _36651.
Proof. exact (h1). Qed.
Lemma lem3469024 {_89991 : Type'} (_36650 : _89991) (_36652 : _89991) (h1 : _36650 = _36652) : _36650 = _36652.
Proof. exact (h1). Qed.
Lemma lem3469025 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36651 : _89991 -> Prop) (h1 : _36649 = _36651) : (@I (_89991 -> Prop) _36649) = (@I (_89991 -> Prop) _36651).
Proof. exact (MK_COMB (@lem3469022 _89991) (@lem3469023 _89991 _36649 _36651 h1)). Qed.
Lemma lem3469026 {_89991 : Type'} (_36650 : _89991) (_36652 : _89991) (_36649 : _89991 -> Prop) (_36651 : _89991 -> Prop) (h1 : _36650 = _36652) (h2 : _36649 = _36651) : (@I (_89991 -> Prop) _36649 _36650) = (@I (_89991 -> Prop) _36651 _36652).
Proof. exact (MK_COMB (@lem3469025 _89991 _36649 _36651 h2) (@lem3469024 _89991 _36650 _36652 h1)). Qed.
Lemma lem3469028 (b : Prop) (a : Prop) : term677 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3469029 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36652 : _89991) (_36649 : _89991 -> Prop) (_36650 : _89991) : term678 _89991 _36651 _36652 _36649 _36650.
Proof. exact (@lem3469028 (@I (_89991 -> Prop) _36651 _36652) (@I (_89991 -> Prop) _36649 _36650)). Qed.
Lemma lem3469030 {_89991 : Type'} (_36650 : _89991) (_36652 : _89991) (_36649 : _89991 -> Prop) (_36651 : _89991 -> Prop) (h1 : _36650 = _36652) (h2 : _36649 = _36651) : term679 _89991 _36651 _36652 _36649 _36650.
Proof. exact (@lem3469029 _89991 _36651 _36652 _36649 _36650 (@lem3469026 _89991 _36650 _36652 _36649 _36651 h1 h2)). Qed.
Lemma lem3469031 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) (_36652 : _89991) (h1 : _36650 = _36652) : term680 _89991 _36651 _36652 _36649 _36650.
Proof. exact (fun h0 : _36649 = _36651 => @lem3469030 _89991 _36650 _36652 _36649 _36651 h1 h0). Qed.
Lemma lem3469033 (a : Prop) (b : Prop) : (a -> b) = (term681 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3469034 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36652 : _89991) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term680 _89991 _36651 _36652 _36649 _36650) = (term682 _89991 _36651 _36652 _36649 _36650).
Proof. exact (@lem3469033 (_36649 = _36651) (term679 _89991 _36651 _36652 _36649 _36650)). Qed.
Lemma lem3469035 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) (_36652 : _89991) (h1 : _36650 = _36652) : term682 _89991 _36651 _36652 _36649 _36650.
Proof. exact (EQ_MP (@lem3469034 _89991 _36651 _36652 _36649 _36650) (@lem3469031 _89991 _36651 _36649 _36650 _36652 h1)). Qed.
Lemma lem3469036 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36652 : _89991) (_36649 : _89991 -> Prop) (_36650 : _89991) : term683 _89991 _36651 _36652 _36649 _36650.
Proof. exact (fun h0 : _36650 = _36652 => @lem3469035 _89991 _36651 _36649 _36650 _36652 h0). Qed.
Lemma lem3469038 (a : Prop) (b : Prop) : (a -> b) = (term681 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3469039 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36652 : _89991) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term683 _89991 _36651 _36652 _36649 _36650) = (term684 _89991 _36651 _36652 _36649 _36650).
Proof. exact (@lem3469038 (_36650 = _36652) (term682 _89991 _36651 _36652 _36649 _36650)). Qed.
Lemma lem3469040 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36652 : _89991) (_36649 : _89991 -> Prop) (_36650 : _89991) : term684 _89991 _36651 _36652 _36649 _36650.
Proof. exact (EQ_MP (@lem3469039 _89991 _36651 _36652 _36649 _36650) (@lem3469036 _89991 _36651 _36652 _36649 _36650)). Qed.
Lemma lem3469106 {_90000 : Type'} (x : _90000) (y : _90000) (z : _90000) : term685 _90000 x y z.
Proof. exact (@lem21385 _90000 x y z). Qed.
Lemma lem3469110 {_89991 : Type'} (x : _89991) (y : _89991) (z : _89991) : term685 _89991 x y z.
Proof. exact (@lem21385 _89991 x y z). Qed.
Lemma lem3469120 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469121 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3469120 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3469123 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469124 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3469123 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3469125 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3469124 _89991 s x'''') (@lem3469121 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469131 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3469132 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term645 _89991 _90000 s x f x''' _36624) = (term686 _89991 _90000 x f x''' s _36624).
Proof. exact (@lem3469131 (x = (term480 _89991 _90000 f x''' _36624)) (term485 _89991 s _36624)). Qed.
Lemma lem3469140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3469141 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term687 _89991 _90000 s x f x''' _36624) = (term688 _89991 _90000 x f x''' s _36624).
Proof. exact (MK_COMB (@lem3469140) (@lem3469132 _89991 _90000 x f x''' s _36624)). Qed.
Lemma lem3469149 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term686 _89991 _90000 x f x''' s _36624) = (term686 _89991 _90000 x f x''' s _36624).
Proof. exact (eq_refl (term686 _89991 _90000 x f x''' s _36624)). Qed.
Lemma lem3469150 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : ((term645 _89991 _90000 s x f x''' _36624) = (term686 _89991 _90000 x f x''' s _36624)) = ((term686 _89991 _90000 x f x''' s _36624) = (term686 _89991 _90000 x f x''' s _36624)).
Proof. exact (MK_COMB (@lem3469141 _89991 _90000 x f x''' s _36624) (@lem3469149 _89991 _90000 x f x''' s _36624)). Qed.
Lemma lem3469152 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3469153 (x : Prop) : (x = x) = True.
Proof. exact (@lem3469152 Prop x). Qed.
Lemma lem3469154 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : ((term686 _89991 _90000 x f x''' s _36624) = (term686 _89991 _90000 x f x''' s _36624)) = True.
Proof. exact (@lem3469153 (term686 _89991 _90000 x f x''' s _36624)). Qed.
Lemma lem3469155 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : ((term645 _89991 _90000 s x f x''' _36624) = (term686 _89991 _90000 x f x''' s _36624)) = True.
Proof. exact (TRANS (@lem3469150 _89991 _90000 x f x''' s _36624) (@lem3469154 _89991 _90000 x f x''' s _36624)). Qed.
Lemma lem3469156 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : True = ((term645 _89991 _90000 s x f x''' _36624) = (term686 _89991 _90000 x f x''' s _36624)).
Proof. exact (SYM (@lem3469155 _89991 _90000 x f x''' s _36624)). Qed.
Lemma lem3469157 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term645 _89991 _90000 s x f x''' _36624) = (term686 _89991 _90000 x f x''' s _36624).
Proof. exact (EQ_MP (@lem3469156 _89991 _90000 x f x''' s _36624) (@lem0)). Qed.
Lemma lem3469158 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term686 _89991 _90000 x f x''' s _36624.
Proof. exact (EQ_MP (@lem3469157 _89991 _90000 x f x''' s _36624) (@lem3468767 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469160 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3469161 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term686 _89991 _90000 x f x''' s _36624) = (term689 _89991 _90000 s x f x''' _36624).
Proof. exact (@lem3469160 (term485 _89991 s _36624) (x = (term480 _89991 _90000 f x''' _36624))). Qed.
Lemma lem3469163 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3469164 {_89991 : Type'} (s : type686 _89991) (_36624 : _89991 -> Prop) : (term664 _89991 s _36624) = (@I ((_89991 -> Prop) -> Prop) s _36624).
Proof. exact (@lem3469163 (@I ((_89991 -> Prop) -> Prop) s _36624)). Qed.
Lemma lem3469165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3469166 {_89991 : Type'} (s : type686 _89991) (_36624 : _89991 -> Prop) : (term665 _89991 s _36624) = (term666 _89991 s _36624).
Proof. exact (MK_COMB (@lem3469165) (@lem3469164 _89991 s _36624)). Qed.
Lemma lem3469167 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (x = (term480 _89991 _90000 f x''' _36624)) = (x = (term480 _89991 _90000 f x''' _36624)).
Proof. exact (eq_refl (x = (term480 _89991 _90000 f x''' _36624))). Qed.
Lemma lem3469168 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term689 _89991 _90000 s x f x''' _36624) = (term690 _89991 _90000 s x f x''' _36624).
Proof. exact (MK_COMB (@lem3469166 _89991 s _36624) (@lem3469167 _89991 _90000 x f x''' _36624)). Qed.
Lemma lem3469169 {_89991 _90000 : Type'} (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term686 _89991 _90000 x f x''' s _36624) = (term690 _89991 _90000 s x f x''' _36624).
Proof. exact (TRANS (@lem3469161 _89991 _90000 s x f x''' _36624) (@lem3469168 _89991 _90000 s x f x''' _36624)). Qed.
Lemma lem3469172 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (EQ_MP (@lem3469169 _89991 _90000 s x f x''' _36624) (@lem3469158 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469173 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (@lem3469172 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469174 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' x''''.
Proof. exact (@lem3469173 _89991 _90000 x'''' t s x f x''' h1). Qed.
Lemma lem3469177 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (@lem3469174 _89991 _90000 x'''' t s x f x''' h1 (@lem3469125 _89991 _90000 x'''' s f h2)). Qed.
Lemma lem3469178 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term691 _89991 _90000 x f x''' x''''.
Proof. exact (fun h0 : term692 _89991 _90000 x f x''' x'''' => @lem3469177 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469180 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469181 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term691 _89991 _90000 x f x''' x'''') = (x = (term480 _89991 _90000 f x''' x'''')).
Proof. exact (@lem3469180 (x = (term480 _89991 _90000 f x''' x''''))). Qed.
Lemma lem3469182 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (EQ_MP (@lem3469181 _89991 _90000 x f x''' x'''') (@lem3469178 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469184 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469185 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3469184 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3469187 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469188 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3469187 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3469189 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3469188 _89991 s x'''') (@lem3469185 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469191 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469192 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3469191 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3469194 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469195 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3469194 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3469196 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3469195 _89991 s x'''') (@lem3469192 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469202 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3469203 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term646 _89991 s x''' _36624) = (term693 _89991 x''' s _36624).
Proof. exact (@lem3469202 (term477 _89991 x''' _36624) (term485 _89991 s _36624)). Qed.
Lemma lem3469209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3469210 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term694 _89991 s x''' _36624) = (term695 _89991 x''' s _36624).
Proof. exact (MK_COMB (@lem3469209) (@lem3469203 _89991 x''' s _36624)). Qed.
Lemma lem3469216 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term693 _89991 x''' s _36624) = (term693 _89991 x''' s _36624).
Proof. exact (eq_refl (term693 _89991 x''' s _36624)). Qed.
Lemma lem3469217 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : ((term646 _89991 s x''' _36624) = (term693 _89991 x''' s _36624)) = ((term693 _89991 x''' s _36624) = (term693 _89991 x''' s _36624)).
Proof. exact (MK_COMB (@lem3469210 _89991 x''' s _36624) (@lem3469216 _89991 x''' s _36624)). Qed.
Lemma lem3469219 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3469220 (x : Prop) : (x = x) = True.
Proof. exact (@lem3469219 Prop x). Qed.
Lemma lem3469221 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : ((term693 _89991 x''' s _36624) = (term693 _89991 x''' s _36624)) = True.
Proof. exact (@lem3469220 (term693 _89991 x''' s _36624)). Qed.
Lemma lem3469222 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : ((term646 _89991 s x''' _36624) = (term693 _89991 x''' s _36624)) = True.
Proof. exact (TRANS (@lem3469217 _89991 x''' s _36624) (@lem3469221 _89991 x''' s _36624)). Qed.
Lemma lem3469223 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : True = ((term646 _89991 s x''' _36624) = (term693 _89991 x''' s _36624)).
Proof. exact (SYM (@lem3469222 _89991 x''' s _36624)). Qed.
Lemma lem3469224 {_89991 : Type'} (x''' : type684 _89991) (s : type686 _89991) (_36624 : _89991 -> Prop) : (term646 _89991 s x''' _36624) = (term693 _89991 x''' s _36624).
Proof. exact (EQ_MP (@lem3469223 _89991 x''' s _36624) (@lem0)). Qed.
Lemma lem3469225 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term693 _89991 x''' s _36624.
Proof. exact (EQ_MP (@lem3469224 _89991 x''' s _36624) (@lem3468773 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469227 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3469228 {_89991 : Type'} (s : type686 _89991) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term693 _89991 x''' s _36624) = (term696 _89991 s x''' _36624).
Proof. exact (@lem3469227 (term485 _89991 s _36624) (term477 _89991 x''' _36624)). Qed.
Lemma lem3469230 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3469231 {_89991 : Type'} (s : type686 _89991) (_36624 : _89991 -> Prop) : (term664 _89991 s _36624) = (@I ((_89991 -> Prop) -> Prop) s _36624).
Proof. exact (@lem3469230 (@I ((_89991 -> Prop) -> Prop) s _36624)). Qed.
Lemma lem3469232 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3469233 {_89991 : Type'} (s : type686 _89991) (_36624 : _89991 -> Prop) : (term665 _89991 s _36624) = (term666 _89991 s _36624).
Proof. exact (MK_COMB (@lem3469232) (@lem3469231 _89991 s _36624)). Qed.
Lemma lem3469234 {_89991 : Type'} (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term477 _89991 x''' _36624) = (term477 _89991 x''' _36624).
Proof. exact (eq_refl (term477 _89991 x''' _36624)). Qed.
Lemma lem3469235 {_89991 : Type'} (s : type686 _89991) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term696 _89991 s x''' _36624) = (term697 _89991 s x''' _36624).
Proof. exact (MK_COMB (@lem3469233 _89991 s _36624) (@lem3469234 _89991 x''' _36624)). Qed.
Lemma lem3469236 {_89991 : Type'} (s : type686 _89991) (x''' : type684 _89991) (_36624 : _89991 -> Prop) : (term693 _89991 x''' s _36624) = (term697 _89991 s x''' _36624).
Proof. exact (TRANS (@lem3469228 _89991 s x''' _36624) (@lem3469235 _89991 s x''' _36624)). Qed.
Lemma lem3469239 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term697 _89991 s x''' _36624.
Proof. exact (EQ_MP (@lem3469236 _89991 s x''' _36624) (@lem3469225 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469240 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term697 _89991 s x''' _36624.
Proof. exact (@lem3469239 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469241 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term697 _89991 s x''' x''''.
Proof. exact (@lem3469240 _89991 _90000 x'''' t s x f x''' h1). Qed.
Lemma lem3469244 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term477 _89991 x''' x''''.
Proof. exact (@lem3469241 _89991 _90000 x'''' t s x f x''' h1 (@lem3469196 _89991 _90000 x'''' s f h2)). Qed.
Lemma lem3469245 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term698 _89991 x''' x''''.
Proof. exact (fun h0 : term699 _89991 x''' x'''' => @lem3469244 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469247 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469248 {_89991 : Type'} (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term698 _89991 x''' x'''') = (term477 _89991 x''' x'''').
Proof. exact (@lem3469247 (term477 _89991 x''' x'''')). Qed.
Lemma lem3469249 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term477 _89991 x''' x''''.
Proof. exact (EQ_MP (@lem3469248 _89991 x''' x'''') (@lem3469245 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469251 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469252 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3469251 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3469254 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469255 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3469254 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3469256 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3469255 _89991 s x'''') (@lem3469252 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469258 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (EQ_MP (@lem3469169 _89991 _90000 s x f x''' _36624) (@lem3469158 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469259 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (@lem3469258 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469260 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' x''''.
Proof. exact (@lem3469259 _89991 _90000 x'''' t s x f x''' h1). Qed.
Lemma lem3469263 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (@lem3469260 _89991 _90000 x'''' t s x f x''' h1 (@lem3469256 _89991 _90000 x'''' s f h2)). Qed.
Lemma lem3469264 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term691 _89991 _90000 x f x''' x''''.
Proof. exact (fun h0 : term692 _89991 _90000 x f x''' x'''' => @lem3469263 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469266 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469267 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term691 _89991 _90000 x f x''' x'''') = (x = (term480 _89991 _90000 f x''' x'''')).
Proof. exact (@lem3469266 (x = (term480 _89991 _90000 f x''' x''''))). Qed.
Lemma lem3469268 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (EQ_MP (@lem3469267 _89991 _90000 x f x''' x'''') (@lem3469264 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469274 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3469275 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : (term647 _89991 _90000 x f s t _36623) = (term700 _89991 _90000 s t x f _36623).
Proof. exact (@lem3469274 (term495 _89991 s t _36623) (term500 _89991 _90000 x f _36623)). Qed.
Lemma lem3469283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3469284 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : (term701 _89991 _90000 x f s t _36623) = (term702 _89991 _90000 s t x f _36623).
Proof. exact (MK_COMB (@lem3469283) (@lem3469275 _89991 _90000 s t x f _36623)). Qed.
Lemma lem3469292 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : (term700 _89991 _90000 s t x f _36623) = (term700 _89991 _90000 s t x f _36623).
Proof. exact (eq_refl (term700 _89991 _90000 s t x f _36623)). Qed.
Lemma lem3469293 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : ((term647 _89991 _90000 x f s t _36623) = (term700 _89991 _90000 s t x f _36623)) = ((term700 _89991 _90000 s t x f _36623) = (term700 _89991 _90000 s t x f _36623)).
Proof. exact (MK_COMB (@lem3469284 _89991 _90000 s t x f _36623) (@lem3469292 _89991 _90000 s t x f _36623)). Qed.
Lemma lem3469295 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3469296 (x : Prop) : (x = x) = True.
Proof. exact (@lem3469295 Prop x). Qed.
Lemma lem3469297 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : ((term700 _89991 _90000 s t x f _36623) = (term700 _89991 _90000 s t x f _36623)) = True.
Proof. exact (@lem3469296 (term700 _89991 _90000 s t x f _36623)). Qed.
Lemma lem3469298 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : ((term647 _89991 _90000 x f s t _36623) = (term700 _89991 _90000 s t x f _36623)) = True.
Proof. exact (TRANS (@lem3469293 _89991 _90000 s t x f _36623) (@lem3469297 _89991 _90000 s t x f _36623)). Qed.
Lemma lem3469299 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : True = ((term647 _89991 _90000 x f s t _36623) = (term700 _89991 _90000 s t x f _36623)).
Proof. exact (SYM (@lem3469298 _89991 _90000 s t x f _36623)). Qed.
Lemma lem3469300 {_89991 _90000 : Type'} (s : type686 _89991) (t : type1402 _89991) (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : (term647 _89991 _90000 x f s t _36623) = (term700 _89991 _90000 s t x f _36623).
Proof. exact (EQ_MP (@lem3469299 _89991 _90000 s t x f _36623) (@lem0)). Qed.
Lemma lem3469301 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term700 _89991 _90000 s t x f _36623.
Proof. exact (EQ_MP (@lem3469300 _89991 _90000 s t x f _36623) (@lem3468779 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3469303 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3469304 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) (_36623 : _89991) : (term700 _89991 _90000 s t x f _36623) = (term703 _89991 _90000 x f s t _36623).
Proof. exact (@lem3469303 (term500 _89991 _90000 x f _36623) (term495 _89991 s t _36623)). Qed.
Lemma lem3469306 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3469307 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : (term704 _89991 _90000 x f _36623) = (x = (@I (_89991 -> _90000) f _36623)).
Proof. exact (@lem3469306 (x = (@I (_89991 -> _90000) f _36623))). Qed.
Lemma lem3469308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3469309 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (_36623 : _89991) : (term705 _89991 _90000 x f _36623) = (term706 _89991 _90000 x f _36623).
Proof. exact (MK_COMB (@lem3469308) (@lem3469307 _89991 _90000 x f _36623)). Qed.
Lemma lem3469310 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (_36623 : _89991) : (term495 _89991 s t _36623) = (term495 _89991 s t _36623).
Proof. exact (eq_refl (term495 _89991 s t _36623)). Qed.
Lemma lem3469311 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) (_36623 : _89991) : (term703 _89991 _90000 x f s t _36623) = (term707 _89991 _90000 x f s t _36623).
Proof. exact (MK_COMB (@lem3469309 _89991 _90000 x f _36623) (@lem3469310 _89991 s t _36623)). Qed.
Lemma lem3469312 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (s : type686 _89991) (t : type1402 _89991) (_36623 : _89991) : (term700 _89991 _90000 s t x f _36623) = (term707 _89991 _90000 x f s t _36623).
Proof. exact (TRANS (@lem3469304 _89991 _90000 x f s t _36623) (@lem3469311 _89991 _90000 x f s t _36623)). Qed.
Lemma lem3469315 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (EQ_MP (@lem3469312 _89991 _90000 x f s t _36623) (@lem3469301 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3469316 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (@lem3469315 _89991 _90000 _36623 t s x f x''' h1). Qed.
Lemma lem3469317 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term708 _89991 _90000 x f s t x''' x''''.
Proof. exact (@lem3469316 _89991 _90000 (@I ((_89991 -> Prop) -> _89991) x''' x'''') t s x f x''' h1). Qed.
Lemma lem3469320 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (@lem3469317 _89991 _90000 x'''' t s x f x''' h1 (@lem3469268 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469321 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term710 _89991 s t x''' x''''.
Proof. exact (fun h0 : term711 _89991 s t x''' x'''' => @lem3469320 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469323 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469324 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term710 _89991 s t x''' x'''') = (term709 _89991 s t x''' x'''').
Proof. exact (@lem3469323 (term709 _89991 s t x''' x'''')). Qed.
Lemma lem3469325 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (EQ_MP (@lem3469324 _89991 s t x''' x'''') (@lem3469321 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469327 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469328 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3469327 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3469330 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469331 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3469330 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3469332 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3469331 _89991 s x'''') (@lem3469328 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469334 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (EQ_MP (@lem3469169 _89991 _90000 s x f x''' _36624) (@lem3469158 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469335 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (@lem3469334 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469336 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' x''''.
Proof. exact (@lem3469335 _89991 _90000 x'''' t s x f x''' h1). Qed.
Lemma lem3469339 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (@lem3469336 _89991 _90000 x'''' t s x f x''' h1 (@lem3469332 _89991 _90000 x'''' s f h2)). Qed.
Lemma lem3469340 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term691 _89991 _90000 x f x''' x''''.
Proof. exact (fun h0 : term692 _89991 _90000 x f x''' x'''' => @lem3469339 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469342 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469343 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term691 _89991 _90000 x f x''' x'''') = (x = (term480 _89991 _90000 f x''' x'''')).
Proof. exact (@lem3469342 (x = (term480 _89991 _90000 f x''' x''''))). Qed.
Lemma lem3469344 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (EQ_MP (@lem3469343 _89991 _90000 x f x''' x'''') (@lem3469340 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469346 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (EQ_MP (@lem3469312 _89991 _90000 x f s t _36623) (@lem3469301 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3469347 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (@lem3469346 _89991 _90000 _36623 t s x f x''' h1). Qed.
Lemma lem3469348 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term708 _89991 _90000 x f s t x''' x''''.
Proof. exact (@lem3469347 _89991 _90000 (@I ((_89991 -> Prop) -> _89991) x''' x'''') t s x f x''' h1). Qed.
Lemma lem3469351 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (@lem3469348 _89991 _90000 x'''' t s x f x''' h1 (@lem3469344 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469352 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term710 _89991 s t x''' x''''.
Proof. exact (fun h0 : term711 _89991 s t x''' x'''' => @lem3469351 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469354 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469355 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term710 _89991 s t x''' x'''') = (term709 _89991 s t x''' x'''').
Proof. exact (@lem3469354 (term709 _89991 s t x''' x'''')). Qed.
Lemma lem3469356 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (EQ_MP (@lem3469355 _89991 s t x''' x'''') (@lem3469352 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469358 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term697 _89991 s x''' _36624.
Proof. exact (EQ_MP (@lem3469236 _89991 s x''' _36624) (@lem3469225 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469359 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term697 _89991 s x''' _36624.
Proof. exact (@lem3469358 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469360 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term712 _89991 s t x''' x''''.
Proof. exact (@lem3469359 _89991 _90000 (term713 _89991 t x''' x'''') t s x f x''' h1). Qed.
Lemma lem3469363 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term714 _89991 t x''' x''''.
Proof. exact (@lem3469360 _89991 _90000 x'''' t s x f x''' h1 (@lem3469356 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469364 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term715 _89991 t x''' x''''.
Proof. exact (fun h0 : term716 _89991 t x''' x'''' => @lem3469363 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469366 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469367 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term715 _89991 t x''' x'''') = (term714 _89991 t x''' x'''').
Proof. exact (@lem3469366 (term714 _89991 t x''' x'''')). Qed.
Lemma lem3469368 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term714 _89991 t x''' x''''.
Proof. exact (EQ_MP (@lem3469367 _89991 t x''' x'''') (@lem3469364 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469370 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469371 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3469370 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3469373 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469374 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3469373 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3469375 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3469374 _89991 s x'''') (@lem3469371 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469377 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (EQ_MP (@lem3469169 _89991 _90000 s x f x''' _36624) (@lem3469158 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469378 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (@lem3469377 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469379 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' x''''.
Proof. exact (@lem3469378 _89991 _90000 x'''' t s x f x''' h1). Qed.
Lemma lem3469382 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (@lem3469379 _89991 _90000 x'''' t s x f x''' h1 (@lem3469375 _89991 _90000 x'''' s f h2)). Qed.
Lemma lem3469383 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term691 _89991 _90000 x f x''' x''''.
Proof. exact (fun h0 : term692 _89991 _90000 x f x''' x'''' => @lem3469382 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469385 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469386 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term691 _89991 _90000 x f x''' x'''') = (x = (term480 _89991 _90000 f x''' x'''')).
Proof. exact (@lem3469385 (x = (term480 _89991 _90000 f x''' x''''))). Qed.
Lemma lem3469387 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (EQ_MP (@lem3469386 _89991 _90000 x f x''' x'''') (@lem3469383 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469389 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469390 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3469389 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3469392 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469393 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3469392 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3469394 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3469393 _89991 s x'''') (@lem3469390 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3469396 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (EQ_MP (@lem3469169 _89991 _90000 s x f x''' _36624) (@lem3469158 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469397 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (@lem3469396 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469398 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' x''''.
Proof. exact (@lem3469397 _89991 _90000 x'''' t s x f x''' h1). Qed.
Lemma lem3469401 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (@lem3469398 _89991 _90000 x'''' t s x f x''' h1 (@lem3469394 _89991 _90000 x'''' s f h2)). Qed.
Lemma lem3469402 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term691 _89991 _90000 x f x''' x''''.
Proof. exact (fun h0 : term692 _89991 _90000 x f x''' x'''' => @lem3469401 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469404 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469405 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term691 _89991 _90000 x f x''' x'''') = (x = (term480 _89991 _90000 f x''' x'''')).
Proof. exact (@lem3469404 (x = (term480 _89991 _90000 f x''' x''''))). Qed.
Lemma lem3469406 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (EQ_MP (@lem3469405 _89991 _90000 x f x''' x'''') (@lem3469402 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469408 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (EQ_MP (@lem3469312 _89991 _90000 x f s t _36623) (@lem3469301 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3469409 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (@lem3469408 _89991 _90000 _36623 t s x f x''' h1). Qed.
Lemma lem3469410 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term708 _89991 _90000 x f s t x''' x''''.
Proof. exact (@lem3469409 _89991 _90000 (@I ((_89991 -> Prop) -> _89991) x''' x'''') t s x f x''' h1). Qed.
Lemma lem3469413 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (@lem3469410 _89991 _90000 x'''' t s x f x''' h1 (@lem3469406 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469414 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term710 _89991 s t x''' x''''.
Proof. exact (fun h0 : term711 _89991 s t x''' x'''' => @lem3469413 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469416 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469417 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term710 _89991 s t x''' x'''') = (term709 _89991 s t x''' x'''').
Proof. exact (@lem3469416 (term709 _89991 s t x''' x'''')). Qed.
Lemma lem3469418 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (EQ_MP (@lem3469417 _89991 s t x''' x'''') (@lem3469414 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469420 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (EQ_MP (@lem3469169 _89991 _90000 s x f x''' _36624) (@lem3469158 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3469421 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (@lem3469420 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3469422 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term717 _89991 _90000 s x f t x''' x''''.
Proof. exact (@lem3469421 _89991 _90000 (term713 _89991 t x''' x'''') t s x f x''' h1). Qed.
Lemma lem3469425 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term718 _89991 _90000 f t x''' x'''').
Proof. exact (@lem3469422 _89991 _90000 x'''' t s x f x''' h1 (@lem3469418 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469426 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term719 _89991 _90000 x f t x''' x''''.
Proof. exact (fun h0 : term720 _89991 _90000 x f t x''' x'''' => @lem3469425 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469428 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469429 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term719 _89991 _90000 x f t x''' x'''') = (x = (term718 _89991 _90000 f t x''' x'''')).
Proof. exact (@lem3469428 (x = (term718 _89991 _90000 f t x''' x''''))). Qed.
Lemma lem3469430 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term718 _89991 _90000 f t x''' x'''').
Proof. exact (EQ_MP (@lem3469429 _89991 _90000 x f t x''' x'''') (@lem3469426 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469448 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3469449 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term721 _90000 x y z) = (term722 _90000 y x z).
Proof. exact (@lem3469448 (y = z) (term723 _90000 x z)). Qed.
Lemma lem3469459 {_90000 : Type'} (x : _90000) (y : _90000) : (term724 _90000 x y) = (term724 _90000 x y).
Proof. exact (eq_refl (term724 _90000 x y)). Qed.
Lemma lem3469460 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term685 _90000 x y z) = (term725 _90000 y x z).
Proof. exact (MK_COMB (@lem3469459 _90000 x y) (@lem3469449 _90000 y x z)). Qed.
Lemma lem3469464 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469465 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term725 _90000 y x z) = (term726 _90000 y x z).
Proof. exact (@lem3469464 (y = z) (term723 _90000 x y) (term723 _90000 x z)). Qed.
Lemma lem3469487 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term685 _90000 x y z) = (term726 _90000 y x z).
Proof. exact (TRANS (@lem3469460 _90000 y x z) (@lem3469465 _90000 y x z)). Qed.
Lemma lem3469488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3469489 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term727 _90000 x y z) = (term728 _90000 y x z).
Proof. exact (MK_COMB (@lem3469488) (@lem3469487 _90000 y x z)). Qed.
Lemma lem3469511 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term726 _90000 y x z) = (term726 _90000 y x z).
Proof. exact (eq_refl (term726 _90000 y x z)). Qed.
Lemma lem3469512 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : ((term685 _90000 x y z) = (term726 _90000 y x z)) = ((term726 _90000 y x z) = (term726 _90000 y x z)).
Proof. exact (MK_COMB (@lem3469489 _90000 y x z) (@lem3469511 _90000 y x z)). Qed.
Lemma lem3469514 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3469515 (x : Prop) : (x = x) = True.
Proof. exact (@lem3469514 Prop x). Qed.
Lemma lem3469516 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : ((term726 _90000 y x z) = (term726 _90000 y x z)) = True.
Proof. exact (@lem3469515 (term726 _90000 y x z)). Qed.
Lemma lem3469517 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : ((term685 _90000 x y z) = (term726 _90000 y x z)) = True.
Proof. exact (TRANS (@lem3469512 _90000 y x z) (@lem3469516 _90000 y x z)). Qed.
Lemma lem3469518 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : True = ((term685 _90000 x y z) = (term726 _90000 y x z)).
Proof. exact (SYM (@lem3469517 _90000 y x z)). Qed.
Lemma lem3469519 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term685 _90000 x y z) = (term726 _90000 y x z).
Proof. exact (EQ_MP (@lem3469518 _90000 y x z) (@lem0)). Qed.
Lemma lem3469520 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : term726 _90000 y x z.
Proof. exact (EQ_MP (@lem3469519 _90000 y x z) (@lem3469106 _90000 x y z)). Qed.
Lemma lem3469522 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3469523 {_90000 : Type'} (x : _90000) (y : _90000) (z : _90000) : (term726 _90000 y x z) = (term729 _90000 x y z).
Proof. exact (@lem3469522 (term730 _90000 y x z) (y = z)). Qed.
Lemma lem3469525 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3469526 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term733 _90000 y x z) = (term734 _90000 y x z).
Proof. exact (@lem3469525 (term723 _90000 x y) (term723 _90000 x z)). Qed.
Lemma lem3469528 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3469529 {_90000 : Type'} (x : _90000) (y : _90000) : (term735 _90000 x y) = (x = y).
Proof. exact (@lem3469528 (x = y)). Qed.
Lemma lem3469530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3469531 {_90000 : Type'} (x : _90000) (y : _90000) : (term736 _90000 x y) = (term737 _90000 x y).
Proof. exact (MK_COMB (@lem3469530) (@lem3469529 _90000 x y)). Qed.
Lemma lem3469533 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3469534 {_90000 : Type'} (x : _90000) (z : _90000) : (term735 _90000 x z) = (x = z).
Proof. exact (@lem3469533 (x = z)). Qed.
Lemma lem3469535 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term734 _90000 y x z) = (term738 _90000 y x z).
Proof. exact (MK_COMB (@lem3469531 _90000 x y) (@lem3469534 _90000 x z)). Qed.
Lemma lem3469536 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term733 _90000 y x z) = (term738 _90000 y x z).
Proof. exact (TRANS (@lem3469526 _90000 y x z) (@lem3469535 _90000 y x z)). Qed.
Lemma lem3469537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3469538 {_90000 : Type'} (y : _90000) (x : _90000) (z : _90000) : (term739 _90000 y x z) = (term740 _90000 y x z).
Proof. exact (MK_COMB (@lem3469537) (@lem3469536 _90000 y x z)). Qed.
Lemma lem3469539 {_90000 : Type'} (y : _90000) (z : _90000) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3469540 {_90000 : Type'} (x : _90000) (y : _90000) (z : _90000) : (term729 _90000 x y z) = (term741 _90000 x y z).
Proof. exact (MK_COMB (@lem3469538 _90000 y x z) (@lem3469539 _90000 y z)). Qed.
Lemma lem3469541 {_90000 : Type'} (x : _90000) (y : _90000) (z : _90000) : (term726 _90000 y x z) = (term741 _90000 x y z).
Proof. exact (TRANS (@lem3469523 _90000 x y z) (@lem3469540 _90000 x y z)). Qed.
Lemma lem3469543 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term742 _89991 _90000 x f t x''' x''''.
Proof. exact (conj (@lem3469387 _89991 _90000 t x x''' x'''' s f h1 h2) (@lem3469430 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469545 {_90000 : Type'} (x : _90000) (y : _90000) (z : _90000) : term741 _90000 x y z.
Proof. exact (EQ_MP (@lem3469541 _90000 x y z) (@lem3469520 _90000 y x z)). Qed.
Lemma lem3469546 {_90000 : Type'} (x : _90000) (y : _90000) (z : _90000) : term741 _90000 x y z.
Proof. exact (@lem3469545 _90000 x y z). Qed.
Lemma lem3469547 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : term743 _89991 _90000 x f t x''' x''''.
Proof. exact (@lem3469546 _90000 x (term480 _89991 _90000 f x''' x'''') (term718 _89991 _90000 f t x''' x'''')). Qed.
Lemma lem3469550 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : (term480 _89991 _90000 f x''' x'''') = (term718 _89991 _90000 f t x''' x'''').
Proof. exact (@lem3469547 _89991 _90000 x f t x''' x'''' (@lem3469543 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469551 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term744 _89991 _90000 f t x''' x''''.
Proof. exact (fun h0 : term745 _89991 _90000 f t x''' x'''' => @lem3469550 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3469553 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3469554 {_89991 _90000 : Type'} (f : _89991 -> _90000) (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term744 _89991 _90000 f t x''' x'''') = ((term480 _89991 _90000 f x''' x'''') = (term718 _89991 _90000 f t x''' x'''')).
Proof. exact (@lem3469553 ((term480 _89991 _90000 f x''' x'''') = (term718 _89991 _90000 f t x''' x''''))). Qed.
Lemma lem3469555 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : (term480 _89991 _90000 f x''' x'''') = (term718 _89991 _90000 f t x''' x'''').
Proof. exact (EQ_MP (@lem3469554 _89991 _90000 f t x''' x'''') (@lem3469551 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3469561 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469562 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term644 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term746 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (@lem3469561 (term508 _89991 _36621 _36619) (term485 _89991 s _36621) (term641 _89991 _90000 s _36622 f _36619 _36620)). Qed.
Lemma lem3469586 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469587 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term641 _89991 _90000 s _36622 f _36619 _36620) = (term747 _89991 _90000 s _36622 f _36619 _36620).
Proof. exact (@lem3469586 (term508 _89991 _36622 _36620) (term485 _89991 s _36622) (term642 _89991 _90000 f _36619 _36620)). Qed.
Lemma lem3469601 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469602 {_89991 _90000 : Type'} (f : _89991 -> _90000) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) : (term748 _89991 _90000 s _36622 f _36619 _36620) = (term749 _89991 _90000 f s _36622 _36619 _36620).
Proof. exact (@lem3469601 (term525 _89991 _90000 _36619 f _36620) (term485 _89991 s _36622) (_36619 = _36620)). Qed.
Lemma lem3469618 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3469619 {_89991 : Type'} (_36619 : _89991) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term750 _89991 s _36622 _36619 _36620) = (term751 _89991 _36619 _36620 s _36622).
Proof. exact (@lem3469618 (_36619 = _36620) (term485 _89991 s _36622)). Qed.
Lemma lem3469627 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term752 _89991 _90000 _36619 f _36620) = (term752 _89991 _90000 _36619 f _36620).
Proof. exact (eq_refl (term752 _89991 _90000 _36619 f _36620)). Qed.
Lemma lem3469628 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term749 _89991 _90000 f s _36622 _36619 _36620) = (term753 _89991 _90000 f _36619 _36620 s _36622).
Proof. exact (MK_COMB (@lem3469627 _89991 _90000 _36619 f _36620) (@lem3469619 _89991 _36619 _36620 s _36622)). Qed.
Lemma lem3469632 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469633 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term753 _89991 _90000 f _36619 _36620 s _36622) = (term754 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (@lem3469632 (_36619 = _36620) (term525 _89991 _90000 _36619 f _36620) (term485 _89991 s _36622)). Qed.
Lemma lem3469653 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term749 _89991 _90000 f s _36622 _36619 _36620) = (term754 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (TRANS (@lem3469628 _89991 _90000 f _36619 _36620 s _36622) (@lem3469633 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469654 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term748 _89991 _90000 s _36622 f _36619 _36620) = (term754 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (TRANS (@lem3469602 _89991 _90000 f s _36622 _36619 _36620) (@lem3469653 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469655 {_89991 : Type'} (_36622 : _89991 -> Prop) (_36620 : _89991) : (term755 _89991 _36622 _36620) = (term755 _89991 _36622 _36620).
Proof. exact (eq_refl (term755 _89991 _36622 _36620)). Qed.
Lemma lem3469656 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term747 _89991 _90000 s _36622 f _36619 _36620) = (term756 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (MK_COMB (@lem3469655 _89991 _36622 _36620) (@lem3469654 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469660 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469661 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term756 _89991 _90000 _36619 f _36620 s _36622) = (term757 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (@lem3469660 (_36619 = _36620) (term508 _89991 _36622 _36620) (term758 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469677 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469678 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term759 _89991 _90000 _36619 f _36620 s _36622) = (term760 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (@lem3469677 (term525 _89991 _90000 _36619 f _36620) (term508 _89991 _36622 _36620) (term485 _89991 s _36622)). Qed.
Lemma lem3469696 {_89991 : Type'} (_36619 : _89991) (_36620 : _89991) : (term761 _89991 _36619 _36620) = (term761 _89991 _36619 _36620).
Proof. exact (eq_refl (term761 _89991 _36619 _36620)). Qed.
Lemma lem3469697 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term757 _89991 _90000 _36619 f _36620 s _36622) = (term762 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (MK_COMB (@lem3469696 _89991 _36619 _36620) (@lem3469678 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469708 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term756 _89991 _90000 _36619 f _36620 s _36622) = (term762 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (TRANS (@lem3469661 _89991 _90000 _36619 f _36620 s _36622) (@lem3469697 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469709 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term747 _89991 _90000 s _36622 f _36619 _36620) = (term762 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (TRANS (@lem3469656 _89991 _90000 _36619 f _36620 s _36622) (@lem3469708 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469710 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term641 _89991 _90000 s _36622 f _36619 _36620) = (term762 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (TRANS (@lem3469587 _89991 _90000 s _36622 f _36619 _36620) (@lem3469709 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469711 {_89991 : Type'} (s : type686 _89991) (_36621 : _89991 -> Prop) : (term486 _89991 s _36621) = (term486 _89991 s _36621).
Proof. exact (eq_refl (term486 _89991 s _36621)). Qed.
Lemma lem3469712 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term763 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term764 _89991 _90000 _36621 _36619 f _36620 s _36622).
Proof. exact (MK_COMB (@lem3469711 _89991 s _36621) (@lem3469710 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469716 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469717 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term764 _89991 _90000 _36621 _36619 f _36620 s _36622) = (term765 _89991 _90000 _36621 _36619 f _36620 s _36622).
Proof. exact (@lem3469716 (_36619 = _36620) (term485 _89991 s _36621) (term760 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469733 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469734 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36621 : _89991 -> Prop) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term766 _89991 _90000 _36621 _36619 f _36620 s _36622) = (term767 _89991 _90000 _36619 f _36621 _36620 s _36622).
Proof. exact (@lem3469733 (term525 _89991 _90000 _36619 f _36620) (term485 _89991 s _36621) (term768 _89991 _36620 s _36622)). Qed.
Lemma lem3469750 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469751 {_89991 : Type'} (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term769 _89991 _36621 _36620 s _36622) = (term770 _89991 _36620 _36621 s _36622).
Proof. exact (@lem3469750 (term508 _89991 _36622 _36620) (term485 _89991 s _36621) (term485 _89991 s _36622)). Qed.
Lemma lem3469767 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term752 _89991 _90000 _36619 f _36620) = (term752 _89991 _90000 _36619 f _36620).
Proof. exact (eq_refl (term752 _89991 _90000 _36619 f _36620)). Qed.
Lemma lem3469768 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term767 _89991 _90000 _36619 f _36621 _36620 s _36622) = (term771 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3469767 _89991 _90000 _36619 f _36620) (@lem3469751 _89991 _36620 _36621 s _36622)). Qed.
Lemma lem3469779 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term766 _89991 _90000 _36621 _36619 f _36620 s _36622) = (term771 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469734 _89991 _90000 _36619 f _36621 _36620 s _36622) (@lem3469768 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3469780 {_89991 : Type'} (_36619 : _89991) (_36620 : _89991) : (term761 _89991 _36619 _36620) = (term761 _89991 _36619 _36620).
Proof. exact (eq_refl (term761 _89991 _36619 _36620)). Qed.
Lemma lem3469781 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term765 _89991 _90000 _36621 _36619 f _36620 s _36622) = (term772 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3469780 _89991 _36619 _36620) (@lem3469779 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3469792 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term764 _89991 _90000 _36621 _36619 f _36620 s _36622) = (term772 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469717 _89991 _90000 _36621 _36619 f _36620 s _36622) (@lem3469781 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3469793 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term763 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term772 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469712 _89991 _90000 _36621 _36619 f _36620 s _36622) (@lem3469792 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3469794 {_89991 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) : (term755 _89991 _36621 _36619) = (term755 _89991 _36621 _36619).
Proof. exact (eq_refl (term755 _89991 _36621 _36619)). Qed.
Lemma lem3469795 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term746 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term773 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3469794 _89991 _36621 _36619) (@lem3469793 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3469799 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469800 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term773 _89991 _90000 _36619 f _36620 _36621 s _36622) = (term774 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (@lem3469799 (_36619 = _36620) (term508 _89991 _36621 _36619) (term771 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3469816 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469817 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term775 _89991 _90000 _36619 f _36620 _36621 s _36622) = (term776 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (@lem3469816 (term525 _89991 _90000 _36619 f _36620) (term508 _89991 _36621 _36619) (term770 _89991 _36620 _36621 s _36622)). Qed.
Lemma lem3469855 {_89991 : Type'} (_36619 : _89991) (_36620 : _89991) : (term761 _89991 _36619 _36620) = (term761 _89991 _36619 _36620).
Proof. exact (eq_refl (term761 _89991 _36619 _36620)). Qed.
Lemma lem3469856 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term774 _89991 _90000 _36619 f _36620 _36621 s _36622) = (term777 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3469855 _89991 _36619 _36620) (@lem3469817 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3469867 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term773 _89991 _90000 _36619 f _36620 _36621 s _36622) = (term777 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469800 _89991 _90000 _36619 f _36620 _36621 s _36622) (@lem3469856 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3469868 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term746 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term777 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469795 _89991 _90000 _36619 f _36620 _36621 s _36622) (@lem3469867 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3469869 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term644 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term777 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469562 _89991 _90000 _36621 s _36622 f _36619 _36620) (@lem3469868 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3469870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3469871 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term778 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term779 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3469870) (@lem3469869 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3469887 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469888 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term780 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term781 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (@lem3469887 (term508 _89991 _36621 _36619) (term485 _89991 s _36621) (term782 _89991 _90000 s _36622 _36619 f _36620)). Qed.
Lemma lem3469912 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469913 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term782 _89991 _90000 s _36622 _36619 f _36620) = (term783 _89991 _90000 s _36622 _36619 f _36620).
Proof. exact (@lem3469912 (term508 _89991 _36622 _36620) (term485 _89991 s _36622) (term525 _89991 _90000 _36619 f _36620)). Qed.
Lemma lem3469927 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3469928 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term784 _89991 _90000 s _36622 _36619 f _36620) = (term758 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (@lem3469927 (term525 _89991 _90000 _36619 f _36620) (term485 _89991 s _36622)). Qed.
Lemma lem3469936 {_89991 : Type'} (_36622 : _89991 -> Prop) (_36620 : _89991) : (term755 _89991 _36622 _36620) = (term755 _89991 _36622 _36620).
Proof. exact (eq_refl (term755 _89991 _36622 _36620)). Qed.
Lemma lem3469937 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term783 _89991 _90000 s _36622 _36619 f _36620) = (term759 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (MK_COMB (@lem3469936 _89991 _36622 _36620) (@lem3469928 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469941 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469942 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term759 _89991 _90000 _36619 f _36620 s _36622) = (term760 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (@lem3469941 (term525 _89991 _90000 _36619 f _36620) (term508 _89991 _36622 _36620) (term485 _89991 s _36622)). Qed.
Lemma lem3469960 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term783 _89991 _90000 s _36622 _36619 f _36620) = (term760 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (TRANS (@lem3469937 _89991 _90000 _36619 f _36620 s _36622) (@lem3469942 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469961 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term782 _89991 _90000 s _36622 _36619 f _36620) = (term760 _89991 _90000 _36619 f _36620 s _36622).
Proof. exact (TRANS (@lem3469913 _89991 _90000 s _36622 _36619 f _36620) (@lem3469960 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469962 {_89991 : Type'} (s : type686 _89991) (_36621 : _89991 -> Prop) : (term486 _89991 s _36621) = (term486 _89991 s _36621).
Proof. exact (eq_refl (term486 _89991 s _36621)). Qed.
Lemma lem3469963 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term785 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term766 _89991 _90000 _36621 _36619 f _36620 s _36622).
Proof. exact (MK_COMB (@lem3469962 _89991 s _36621) (@lem3469961 _89991 _90000 _36619 f _36620 s _36622)). Qed.
Lemma lem3469967 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469968 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36621 : _89991 -> Prop) (_36620 : _89991) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term766 _89991 _90000 _36621 _36619 f _36620 s _36622) = (term767 _89991 _90000 _36619 f _36621 _36620 s _36622).
Proof. exact (@lem3469967 (term525 _89991 _90000 _36619 f _36620) (term485 _89991 s _36621) (term768 _89991 _36620 s _36622)). Qed.
Lemma lem3469984 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3469985 {_89991 : Type'} (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term769 _89991 _36621 _36620 s _36622) = (term770 _89991 _36620 _36621 s _36622).
Proof. exact (@lem3469984 (term508 _89991 _36622 _36620) (term485 _89991 s _36621) (term485 _89991 s _36622)). Qed.
Lemma lem3470001 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term752 _89991 _90000 _36619 f _36620) = (term752 _89991 _90000 _36619 f _36620).
Proof. exact (eq_refl (term752 _89991 _90000 _36619 f _36620)). Qed.
Lemma lem3470002 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term767 _89991 _90000 _36619 f _36621 _36620 s _36622) = (term771 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3470001 _89991 _90000 _36619 f _36620) (@lem3469985 _89991 _36620 _36621 s _36622)). Qed.
Lemma lem3470013 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term766 _89991 _90000 _36621 _36619 f _36620 s _36622) = (term771 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469968 _89991 _90000 _36619 f _36621 _36620 s _36622) (@lem3470002 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3470014 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term785 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term771 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469963 _89991 _90000 _36621 _36619 f _36620 s _36622) (@lem3470013 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3470015 {_89991 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) : (term755 _89991 _36621 _36619) = (term755 _89991 _36621 _36619).
Proof. exact (eq_refl (term755 _89991 _36621 _36619)). Qed.
Lemma lem3470016 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term781 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term775 _89991 _90000 _36619 f _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3470015 _89991 _36621 _36619) (@lem3470014 _89991 _90000 _36619 f _36620 _36621 s _36622)). Qed.
Lemma lem3470020 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3470021 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term775 _89991 _90000 _36619 f _36620 _36621 s _36622) = (term776 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (@lem3470020 (term525 _89991 _90000 _36619 f _36620) (term508 _89991 _36621 _36619) (term770 _89991 _36620 _36621 s _36622)). Qed.
Lemma lem3470059 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term781 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term776 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3470016 _89991 _90000 _36619 f _36620 _36621 s _36622) (@lem3470021 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3470060 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term780 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term776 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (TRANS (@lem3469888 _89991 _90000 _36621 s _36622 _36619 f _36620) (@lem3470059 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3470061 {_89991 : Type'} (_36619 : _89991) (_36620 : _89991) : (term761 _89991 _36619 _36620) = (term761 _89991 _36619 _36620).
Proof. exact (eq_refl (term761 _89991 _36619 _36620)). Qed.
Lemma lem3470062 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : (term786 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term777 _89991 _90000 f _36619 _36620 _36621 s _36622).
Proof. exact (MK_COMB (@lem3470061 _89991 _36619 _36620) (@lem3470060 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3470073 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : ((term644 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term786 _89991 _90000 _36621 s _36622 _36619 f _36620)) = ((term777 _89991 _90000 f _36619 _36620 _36621 s _36622) = (term777 _89991 _90000 f _36619 _36620 _36621 s _36622)).
Proof. exact (MK_COMB (@lem3469871 _89991 _90000 f _36619 _36620 _36621 s _36622) (@lem3470062 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3470075 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3470076 (x : Prop) : (x = x) = True.
Proof. exact (@lem3470075 Prop x). Qed.
Lemma lem3470077 {_89991 _90000 : Type'} (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) : ((term777 _89991 _90000 f _36619 _36620 _36621 s _36622) = (term777 _89991 _90000 f _36619 _36620 _36621 s _36622)) = True.
Proof. exact (@lem3470076 (term777 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3470078 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : ((term644 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term786 _89991 _90000 _36621 s _36622 _36619 f _36620)) = True.
Proof. exact (TRANS (@lem3470073 _89991 _90000 f _36619 _36620 _36621 s _36622) (@lem3470077 _89991 _90000 f _36619 _36620 _36621 s _36622)). Qed.
Lemma lem3470079 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : True = ((term644 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term786 _89991 _90000 _36621 s _36622 _36619 f _36620)).
Proof. exact (SYM (@lem3470078 _89991 _90000 _36621 s _36622 _36619 f _36620)). Qed.
Lemma lem3470080 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term644 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term786 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (EQ_MP (@lem3470079 _89991 _90000 _36621 s _36622 _36619 f _36620) (@lem0)). Qed.
Lemma lem3470081 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36622 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term786 _89991 _90000 _36621 s _36622 _36619 f _36620.
Proof. exact (EQ_MP (@lem3470080 _89991 _90000 _36621 s _36622 _36619 f _36620) (@lem3468761 _89991 _90000 _36621 _36622 _36619 _36620 x'''' s f h1)). Qed.
Lemma lem3470083 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3470084 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term786 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term787 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (@lem3470083 (term780 _89991 _90000 _36621 s _36622 _36619 f _36620) (_36619 = _36620)). Qed.
Lemma lem3470086 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3470087 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term788 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term789 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (@lem3470086 (term485 _89991 s _36621) (term790 _89991 _90000 _36621 s _36622 _36619 f _36620)). Qed.
Lemma lem3470089 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470090 {_89991 : Type'} (s : type686 _89991) (_36621 : _89991 -> Prop) : (term664 _89991 s _36621) = (@I ((_89991 -> Prop) -> Prop) s _36621).
Proof. exact (@lem3470089 (@I ((_89991 -> Prop) -> Prop) s _36621)). Qed.
Lemma lem3470091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470092 {_89991 : Type'} (s : type686 _89991) (_36621 : _89991 -> Prop) : (term791 _89991 s _36621) = (term512 _89991 s _36621).
Proof. exact (MK_COMB (@lem3470091) (@lem3470090 _89991 s _36621)). Qed.
Lemma lem3470094 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3470095 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term792 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term793 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (@lem3470094 (term508 _89991 _36621 _36619) (term782 _89991 _90000 s _36622 _36619 f _36620)). Qed.
Lemma lem3470097 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470098 {_89991 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) : (term794 _89991 _36621 _36619) = (@I (_89991 -> Prop) _36621 _36619).
Proof. exact (@lem3470097 (@I (_89991 -> Prop) _36621 _36619)). Qed.
Lemma lem3470099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470100 {_89991 : Type'} (_36621 : _89991 -> Prop) (_36619 : _89991) : (term795 _89991 _36621 _36619) = (term796 _89991 _36621 _36619).
Proof. exact (MK_COMB (@lem3470099) (@lem3470098 _89991 _36621 _36619)). Qed.
Lemma lem3470102 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3470103 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term797 _89991 _90000 s _36622 _36619 f _36620) = (term798 _89991 _90000 s _36622 _36619 f _36620).
Proof. exact (@lem3470102 (term485 _89991 s _36622) (term799 _89991 _90000 _36622 _36619 f _36620)). Qed.
Lemma lem3470105 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470106 {_89991 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) : (term664 _89991 s _36622) = (@I ((_89991 -> Prop) -> Prop) s _36622).
Proof. exact (@lem3470105 (@I ((_89991 -> Prop) -> Prop) s _36622)). Qed.
Lemma lem3470107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470108 {_89991 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) : (term791 _89991 s _36622) = (term512 _89991 s _36622).
Proof. exact (MK_COMB (@lem3470107) (@lem3470106 _89991 s _36622)). Qed.
Lemma lem3470110 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3470111 {_89991 _90000 : Type'} (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term800 _89991 _90000 _36622 _36619 f _36620) = (term801 _89991 _90000 _36622 _36619 f _36620).
Proof. exact (@lem3470110 (term508 _89991 _36622 _36620) (term525 _89991 _90000 _36619 f _36620)). Qed.
Lemma lem3470113 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470114 {_89991 : Type'} (_36622 : _89991 -> Prop) (_36620 : _89991) : (term794 _89991 _36622 _36620) = (@I (_89991 -> Prop) _36622 _36620).
Proof. exact (@lem3470113 (@I (_89991 -> Prop) _36622 _36620)). Qed.
Lemma lem3470115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470116 {_89991 : Type'} (_36622 : _89991 -> Prop) (_36620 : _89991) : (term795 _89991 _36622 _36620) = (term796 _89991 _36622 _36620).
Proof. exact (MK_COMB (@lem3470115) (@lem3470114 _89991 _36622 _36620)). Qed.
Lemma lem3470118 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470119 {_89991 _90000 : Type'} (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term802 _89991 _90000 _36619 f _36620) = ((@I (_89991 -> _90000) f _36619) = (@I (_89991 -> _90000) f _36620)).
Proof. exact (@lem3470118 ((@I (_89991 -> _90000) f _36619) = (@I (_89991 -> _90000) f _36620))). Qed.
Lemma lem3470120 {_89991 _90000 : Type'} (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term801 _89991 _90000 _36622 _36619 f _36620) = (term803 _89991 _90000 _36622 _36619 f _36620).
Proof. exact (MK_COMB (@lem3470116 _89991 _36622 _36620) (@lem3470119 _89991 _90000 _36619 f _36620)). Qed.
Lemma lem3470121 {_89991 _90000 : Type'} (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term800 _89991 _90000 _36622 _36619 f _36620) = (term803 _89991 _90000 _36622 _36619 f _36620).
Proof. exact (TRANS (@lem3470111 _89991 _90000 _36622 _36619 f _36620) (@lem3470120 _89991 _90000 _36622 _36619 f _36620)). Qed.
Lemma lem3470122 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term798 _89991 _90000 s _36622 _36619 f _36620) = (term804 _89991 _90000 s _36622 _36619 f _36620).
Proof. exact (MK_COMB (@lem3470108 _89991 s _36622) (@lem3470121 _89991 _90000 _36622 _36619 f _36620)). Qed.
Lemma lem3470123 {_89991 _90000 : Type'} (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term797 _89991 _90000 s _36622 _36619 f _36620) = (term804 _89991 _90000 s _36622 _36619 f _36620).
Proof. exact (TRANS (@lem3470103 _89991 _90000 s _36622 _36619 f _36620) (@lem3470122 _89991 _90000 s _36622 _36619 f _36620)). Qed.
Lemma lem3470124 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term793 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term805 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (MK_COMB (@lem3470100 _89991 _36621 _36619) (@lem3470123 _89991 _90000 s _36622 _36619 f _36620)). Qed.
Lemma lem3470125 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term792 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term805 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (TRANS (@lem3470095 _89991 _90000 _36621 s _36622 _36619 f _36620) (@lem3470124 _89991 _90000 _36621 s _36622 _36619 f _36620)). Qed.
Lemma lem3470126 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term789 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term806 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (MK_COMB (@lem3470092 _89991 s _36621) (@lem3470125 _89991 _90000 _36621 s _36622 _36619 f _36620)). Qed.
Lemma lem3470127 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term788 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term806 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (TRANS (@lem3470087 _89991 _90000 _36621 s _36622 _36619 f _36620) (@lem3470126 _89991 _90000 _36621 s _36622 _36619 f _36620)). Qed.
Lemma lem3470128 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3470129 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (_36619 : _89991) (f : _89991 -> _90000) (_36620 : _89991) : (term807 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term808 _89991 _90000 _36621 s _36622 _36619 f _36620).
Proof. exact (MK_COMB (@lem3470128) (@lem3470127 _89991 _90000 _36621 s _36622 _36619 f _36620)). Qed.
Lemma lem3470130 {_89991 : Type'} (_36619 : _89991) (_36620 : _89991) : (_36619 = _36620) = (_36619 = _36620).
Proof. exact (eq_refl (_36619 = _36620)). Qed.
Lemma lem3470131 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term787 _89991 _90000 _36621 s _36622 f _36619 _36620) = (term809 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (MK_COMB (@lem3470129 _89991 _90000 _36621 s _36622 _36619 f _36620) (@lem3470130 _89991 _36619 _36620)). Qed.
Lemma lem3470132 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (s : type686 _89991) (_36622 : _89991 -> Prop) (f : _89991 -> _90000) (_36619 : _89991) (_36620 : _89991) : (term786 _89991 _90000 _36621 s _36622 _36619 f _36620) = (term809 _89991 _90000 _36621 s _36622 f _36619 _36620).
Proof. exact (TRANS (@lem3470084 _89991 _90000 _36621 s _36622 f _36619 _36620) (@lem3470131 _89991 _90000 _36621 s _36622 f _36619 _36620)). Qed.
Lemma lem3470134 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term810 _89991 _90000 f t x''' x''''.
Proof. exact (conj (@lem3469368 _89991 _90000 t x x''' x'''' s f h1 h2) (@lem3469555 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470135 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term811 _89991 _90000 s f t x''' x''''.
Proof. exact (conj (@lem3469325 _89991 _90000 t x x''' x'''' s f h1 h2) (@lem3470134 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470136 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term812 _89991 _90000 s f t x''' x''''.
Proof. exact (conj (@lem3469249 _89991 _90000 t x x''' x'''' s f h1 h2) (@lem3470135 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470137 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term813 _89991 _90000 s f t x''' x''''.
Proof. exact (conj (@lem3469189 _89991 _90000 x'''' s f h2) (@lem3470136 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470139 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36622 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term809 _89991 _90000 _36621 s _36622 f _36619 _36620.
Proof. exact (EQ_MP (@lem3470132 _89991 _90000 _36621 s _36622 f _36619 _36620) (@lem3470081 _89991 _90000 _36621 _36622 _36619 _36620 x'''' s f h1)). Qed.
Lemma lem3470140 {_89991 _90000 : Type'} (_36621 : _89991 -> Prop) (_36622 : _89991 -> Prop) (_36619 : _89991) (_36620 : _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term809 _89991 _90000 _36621 s _36622 f _36619 _36620.
Proof. exact (@lem3470139 _89991 _90000 _36621 _36622 _36619 _36620 x'''' s f h1). Qed.
Lemma lem3470141 {_89991 _90000 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term814 _89991 _90000 s f t x''' x''''.
Proof. exact (@lem3470140 _89991 _90000 x'''' (term713 _89991 t x''' x'''') (@I ((_89991 -> Prop) -> _89991) x''' x'''') (term815 _89991 t x''' x'''') x'''' s f h1). Qed.
Lemma lem3470144 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : (@I ((_89991 -> Prop) -> _89991) x''' x'''') = (term815 _89991 t x''' x'''').
Proof. exact (@lem3470141 _89991 _90000 t x''' x'''' s f h2 (@lem3470137 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470145 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term816 _89991 t x''' x''''.
Proof. exact (fun h0 : term817 _89991 t x''' x'''' => @lem3470144 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3470147 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470148 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term816 _89991 t x''' x'''') = ((@I ((_89991 -> Prop) -> _89991) x''' x'''') = (term815 _89991 t x''' x'''')).
Proof. exact (@lem3470147 ((@I ((_89991 -> Prop) -> _89991) x''' x'''') = (term815 _89991 t x''' x''''))). Qed.
Lemma lem3470149 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : (@I ((_89991 -> Prop) -> _89991) x''' x'''') = (term815 _89991 t x''' x'''').
Proof. exact (EQ_MP (@lem3470148 _89991 t x''' x'''') (@lem3470145 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470151 {_89991 : Type'} (x : _89991) : x = x.
Proof. exact (@lem21386 _89991 x). Qed.
Lemma lem3470152 {_89991 : Type'} (x : _89991) : x = x.
Proof. exact (@lem3470151 _89991 x). Qed.
Lemma lem3470153 {_89991 : Type'} (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (@I ((_89991 -> Prop) -> _89991) x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x'''').
Proof. exact (@lem3470152 _89991 (@I ((_89991 -> Prop) -> _89991) x''' x'''')). Qed.
Lemma lem3470154 {_89991 : Type'} (x''' : type684 _89991) (x'''' : _89991 -> Prop) : term818 _89991 x''' x''''.
Proof. exact (fun h0 : term819 _89991 x''' x'''' => @lem3470153 _89991 x''' x''''). Qed.
Lemma lem3470156 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470157 {_89991 : Type'} (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term818 _89991 x''' x'''') = ((@I ((_89991 -> Prop) -> _89991) x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x'''')).
Proof. exact (@lem3470156 ((@I ((_89991 -> Prop) -> _89991) x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x''''))). Qed.
Lemma lem3470158 {_89991 : Type'} (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (@I ((_89991 -> Prop) -> _89991) x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x'''').
Proof. exact (EQ_MP (@lem3470157 _89991 x''' x'''') (@lem3470154 _89991 x''' x'''')). Qed.
Lemma lem3470176 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3470177 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term721 _89991 x y z) = (term722 _89991 y x z).
Proof. exact (@lem3470176 (y = z) (term723 _89991 x z)). Qed.
Lemma lem3470187 {_89991 : Type'} (x : _89991) (y : _89991) : (term724 _89991 x y) = (term724 _89991 x y).
Proof. exact (eq_refl (term724 _89991 x y)). Qed.
Lemma lem3470188 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term685 _89991 x y z) = (term725 _89991 y x z).
Proof. exact (MK_COMB (@lem3470187 _89991 x y) (@lem3470177 _89991 y x z)). Qed.
Lemma lem3470192 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3470193 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term725 _89991 y x z) = (term726 _89991 y x z).
Proof. exact (@lem3470192 (y = z) (term723 _89991 x y) (term723 _89991 x z)). Qed.
Lemma lem3470215 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term685 _89991 x y z) = (term726 _89991 y x z).
Proof. exact (TRANS (@lem3470188 _89991 y x z) (@lem3470193 _89991 y x z)). Qed.
Lemma lem3470216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3470217 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term727 _89991 x y z) = (term728 _89991 y x z).
Proof. exact (MK_COMB (@lem3470216) (@lem3470215 _89991 y x z)). Qed.
Lemma lem3470239 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term726 _89991 y x z) = (term726 _89991 y x z).
Proof. exact (eq_refl (term726 _89991 y x z)). Qed.
Lemma lem3470240 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : ((term685 _89991 x y z) = (term726 _89991 y x z)) = ((term726 _89991 y x z) = (term726 _89991 y x z)).
Proof. exact (MK_COMB (@lem3470217 _89991 y x z) (@lem3470239 _89991 y x z)). Qed.
Lemma lem3470242 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3470243 (x : Prop) : (x = x) = True.
Proof. exact (@lem3470242 Prop x). Qed.
Lemma lem3470244 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : ((term726 _89991 y x z) = (term726 _89991 y x z)) = True.
Proof. exact (@lem3470243 (term726 _89991 y x z)). Qed.
Lemma lem3470245 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : ((term685 _89991 x y z) = (term726 _89991 y x z)) = True.
Proof. exact (TRANS (@lem3470240 _89991 y x z) (@lem3470244 _89991 y x z)). Qed.
Lemma lem3470246 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : True = ((term685 _89991 x y z) = (term726 _89991 y x z)).
Proof. exact (SYM (@lem3470245 _89991 y x z)). Qed.
Lemma lem3470247 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term685 _89991 x y z) = (term726 _89991 y x z).
Proof. exact (EQ_MP (@lem3470246 _89991 y x z) (@lem0)). Qed.
Lemma lem3470248 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : term726 _89991 y x z.
Proof. exact (EQ_MP (@lem3470247 _89991 y x z) (@lem3469110 _89991 x y z)). Qed.
Lemma lem3470250 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3470251 {_89991 : Type'} (x : _89991) (y : _89991) (z : _89991) : (term726 _89991 y x z) = (term729 _89991 x y z).
Proof. exact (@lem3470250 (term730 _89991 y x z) (y = z)). Qed.
Lemma lem3470253 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3470254 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term733 _89991 y x z) = (term734 _89991 y x z).
Proof. exact (@lem3470253 (term723 _89991 x y) (term723 _89991 x z)). Qed.
Lemma lem3470256 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470257 {_89991 : Type'} (x : _89991) (y : _89991) : (term735 _89991 x y) = (x = y).
Proof. exact (@lem3470256 (x = y)). Qed.
Lemma lem3470258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470259 {_89991 : Type'} (x : _89991) (y : _89991) : (term736 _89991 x y) = (term737 _89991 x y).
Proof. exact (MK_COMB (@lem3470258) (@lem3470257 _89991 x y)). Qed.
Lemma lem3470261 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470262 {_89991 : Type'} (x : _89991) (z : _89991) : (term735 _89991 x z) = (x = z).
Proof. exact (@lem3470261 (x = z)). Qed.
Lemma lem3470263 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term734 _89991 y x z) = (term738 _89991 y x z).
Proof. exact (MK_COMB (@lem3470259 _89991 x y) (@lem3470262 _89991 x z)). Qed.
Lemma lem3470264 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term733 _89991 y x z) = (term738 _89991 y x z).
Proof. exact (TRANS (@lem3470254 _89991 y x z) (@lem3470263 _89991 y x z)). Qed.
Lemma lem3470265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3470266 {_89991 : Type'} (y : _89991) (x : _89991) (z : _89991) : (term739 _89991 y x z) = (term740 _89991 y x z).
Proof. exact (MK_COMB (@lem3470265) (@lem3470264 _89991 y x z)). Qed.
Lemma lem3470267 {_89991 : Type'} (y : _89991) (z : _89991) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3470268 {_89991 : Type'} (x : _89991) (y : _89991) (z : _89991) : (term729 _89991 x y z) = (term741 _89991 x y z).
Proof. exact (MK_COMB (@lem3470266 _89991 y x z) (@lem3470267 _89991 y z)). Qed.
Lemma lem3470269 {_89991 : Type'} (x : _89991) (y : _89991) (z : _89991) : (term726 _89991 y x z) = (term741 _89991 x y z).
Proof. exact (TRANS (@lem3470251 _89991 x y z) (@lem3470268 _89991 x y z)). Qed.
Lemma lem3470271 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term820 _89991 t x''' x''''.
Proof. exact (conj (@lem3470149 _89991 _90000 t x x''' x'''' s f h1 h2) (@lem3470158 _89991 x''' x'''')). Qed.
Lemma lem3470273 {_89991 : Type'} (x : _89991) (y : _89991) (z : _89991) : term741 _89991 x y z.
Proof. exact (EQ_MP (@lem3470269 _89991 x y z) (@lem3470248 _89991 y x z)). Qed.
Lemma lem3470274 {_89991 : Type'} (x : _89991) (y : _89991) (z : _89991) : term741 _89991 x y z.
Proof. exact (@lem3470273 _89991 x y z). Qed.
Lemma lem3470275 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : term821 _89991 t x''' x''''.
Proof. exact (@lem3470274 _89991 (@I ((_89991 -> Prop) -> _89991) x''' x'''') (term815 _89991 t x''' x'''') (@I ((_89991 -> Prop) -> _89991) x''' x'''')). Qed.
Lemma lem3470278 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : (term815 _89991 t x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x'''').
Proof. exact (@lem3470275 _89991 t x''' x'''' (@lem3470271 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470279 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term822 _89991 t x''' x''''.
Proof. exact (fun h0 : term823 _89991 t x''' x'''' => @lem3470278 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3470281 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470282 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term822 _89991 t x''' x'''') = ((term815 _89991 t x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x'''')).
Proof. exact (@lem3470281 ((term815 _89991 t x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x''''))). Qed.
Lemma lem3470283 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : (term815 _89991 t x''' x'''') = (@I ((_89991 -> Prop) -> _89991) x''' x'''').
Proof. exact (EQ_MP (@lem3470282 _89991 t x''' x'''') (@lem3470279 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470285 {_89991 : Type'} (x : _89991 -> Prop) : x = x.
Proof. exact (@lem21386 (_89991 -> Prop) x). Qed.
Lemma lem3470286 {_89991 : Type'} (x : _89991 -> Prop) : x = x.
Proof. exact (@lem3470285 _89991 x). Qed.
Lemma lem3470287 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term713 _89991 t x''' x'''') = (term713 _89991 t x''' x'''').
Proof. exact (@lem3470286 _89991 (term713 _89991 t x''' x'''')). Qed.
Lemma lem3470288 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : term824 _89991 t x''' x''''.
Proof. exact (fun h0 : term825 _89991 t x''' x'''' => @lem3470287 _89991 t x''' x''''). Qed.
Lemma lem3470290 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470291 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term824 _89991 t x''' x'''') = ((term713 _89991 t x''' x'''') = (term713 _89991 t x''' x'''')).
Proof. exact (@lem3470290 ((term713 _89991 t x''' x'''') = (term713 _89991 t x''' x''''))). Qed.
Lemma lem3470292 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term713 _89991 t x''' x'''') = (term713 _89991 t x''' x'''').
Proof. exact (EQ_MP (@lem3470291 _89991 t x''' x'''') (@lem3470288 _89991 t x''' x'''')). Qed.
Lemma lem3470294 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (proj1 (@lem3468175 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3470295 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : term658 _89991 s x''''.
Proof. exact (fun h0 : term485 _89991 s x'''' => @lem3470294 _89991 _90000 x'''' s f h1). Qed.
Lemma lem3470297 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470298 {_89991 : Type'} (s : type686 _89991) (x'''' : _89991 -> Prop) : (term658 _89991 s x'''') = (@I ((_89991 -> Prop) -> Prop) s x'''').
Proof. exact (@lem3470297 (@I ((_89991 -> Prop) -> Prop) s x'''')). Qed.
Lemma lem3470299 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term474 _89991 _90000 x'''' s f) : @I ((_89991 -> Prop) -> Prop) s x''''.
Proof. exact (EQ_MP (@lem3470298 _89991 s x'''') (@lem3470295 _89991 _90000 x'''' s f h1)). Qed.
Lemma lem3470301 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (EQ_MP (@lem3469169 _89991 _90000 s x f x''' _36624) (@lem3469158 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3470302 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' _36624.
Proof. exact (@lem3470301 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3470303 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term690 _89991 _90000 s x f x''' x''''.
Proof. exact (@lem3470302 _89991 _90000 x'''' t s x f x''' h1). Qed.
Lemma lem3470306 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (@lem3470303 _89991 _90000 x'''' t s x f x''' h1 (@lem3470299 _89991 _90000 x'''' s f h2)). Qed.
Lemma lem3470307 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term691 _89991 _90000 x f x''' x''''.
Proof. exact (fun h0 : term692 _89991 _90000 x f x''' x'''' => @lem3470306 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3470309 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470310 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term691 _89991 _90000 x f x''' x'''') = (x = (term480 _89991 _90000 f x''' x'''')).
Proof. exact (@lem3470309 (x = (term480 _89991 _90000 f x''' x''''))). Qed.
Lemma lem3470311 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : x = (term480 _89991 _90000 f x''' x'''').
Proof. exact (EQ_MP (@lem3470310 _89991 _90000 x f x''' x'''') (@lem3470307 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470313 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (EQ_MP (@lem3469312 _89991 _90000 x f s t _36623) (@lem3469301 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3470314 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term707 _89991 _90000 x f s t _36623.
Proof. exact (@lem3470313 _89991 _90000 _36623 t s x f x''' h1). Qed.
Lemma lem3470315 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term708 _89991 _90000 x f s t x''' x''''.
Proof. exact (@lem3470314 _89991 _90000 (@I ((_89991 -> Prop) -> _89991) x''' x'''') t s x f x''' h1). Qed.
Lemma lem3470318 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (@lem3470315 _89991 _90000 x'''' t s x f x''' h1 (@lem3470311 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470319 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term710 _89991 s t x''' x''''.
Proof. exact (fun h0 : term711 _89991 s t x''' x'''' => @lem3470318 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3470321 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470322 {_89991 : Type'} (s : type686 _89991) (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term710 _89991 s t x''' x'''') = (term709 _89991 s t x''' x'''').
Proof. exact (@lem3470321 (term709 _89991 s t x''' x'''')). Qed.
Lemma lem3470323 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term709 _89991 s t x''' x''''.
Proof. exact (EQ_MP (@lem3470322 _89991 s t x''' x'''') (@lem3470319 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470325 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term697 _89991 s x''' _36624.
Proof. exact (EQ_MP (@lem3469236 _89991 s x''' _36624) (@lem3469225 _89991 _90000 _36624 t s x f x''' h1)). Qed.
Lemma lem3470326 {_89991 _90000 : Type'} (_36624 : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term697 _89991 s x''' _36624.
Proof. exact (@lem3470325 _89991 _90000 _36624 t s x f x''' h1). Qed.
Lemma lem3470327 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term712 _89991 s t x''' x''''.
Proof. exact (@lem3470326 _89991 _90000 (term713 _89991 t x''' x'''') t s x f x''' h1). Qed.
Lemma lem3470330 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term714 _89991 t x''' x''''.
Proof. exact (@lem3470327 _89991 _90000 x'''' t s x f x''' h1 (@lem3470323 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470331 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term715 _89991 t x''' x''''.
Proof. exact (fun h0 : term716 _89991 t x''' x'''' => @lem3470330 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3470333 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470334 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term715 _89991 t x''' x'''') = (term714 _89991 t x''' x'''').
Proof. exact (@lem3470333 (term714 _89991 t x''' x'''')). Qed.
Lemma lem3470335 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term714 _89991 t x''' x''''.
Proof. exact (EQ_MP (@lem3470334 _89991 t x''' x'''') (@lem3470331 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470353 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3470354 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term682 _89991 _36651 _36652 _36649 _36650) = (term826 _89991 _36652 _36651 _36649 _36650).
Proof. exact (@lem3470353 (@I (_89991 -> Prop) _36651 _36652) (term827 _89991 _36649 _36651) (term508 _89991 _36649 _36650)). Qed.
Lemma lem3470372 {_89991 : Type'} (_36650 : _89991) (_36652 : _89991) : (term724 _89991 _36650 _36652) = (term724 _89991 _36650 _36652).
Proof. exact (eq_refl (term724 _89991 _36650 _36652)). Qed.
Lemma lem3470373 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term684 _89991 _36651 _36652 _36649 _36650) = (term828 _89991 _36652 _36651 _36649 _36650).
Proof. exact (MK_COMB (@lem3470372 _89991 _36650 _36652) (@lem3470354 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470377 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3470378 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term828 _89991 _36652 _36651 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650).
Proof. exact (@lem3470377 (@I (_89991 -> Prop) _36651 _36652) (term723 _89991 _36650 _36652) (term830 _89991 _36651 _36649 _36650)). Qed.
Lemma lem3470408 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term684 _89991 _36651 _36652 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650).
Proof. exact (TRANS (@lem3470373 _89991 _36652 _36651 _36649 _36650) (@lem3470378 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3470410 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term831 _89991 _36651 _36652 _36649 _36650) = (term832 _89991 _36652 _36651 _36649 _36650).
Proof. exact (MK_COMB (@lem3470409) (@lem3470408 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470440 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term829 _89991 _36652 _36651 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650).
Proof. exact (eq_refl (term829 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470441 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : ((term684 _89991 _36651 _36652 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650)) = ((term829 _89991 _36652 _36651 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650)).
Proof. exact (MK_COMB (@lem3470410 _89991 _36652 _36651 _36649 _36650) (@lem3470440 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470443 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3470444 (x : Prop) : (x = x) = True.
Proof. exact (@lem3470443 Prop x). Qed.
Lemma lem3470445 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : ((term829 _89991 _36652 _36651 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650)) = True.
Proof. exact (@lem3470444 (term829 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470446 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : ((term684 _89991 _36651 _36652 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650)) = True.
Proof. exact (TRANS (@lem3470441 _89991 _36652 _36651 _36649 _36650) (@lem3470445 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470447 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : True = ((term684 _89991 _36651 _36652 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650)).
Proof. exact (SYM (@lem3470446 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470448 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term684 _89991 _36651 _36652 _36649 _36650) = (term829 _89991 _36652 _36651 _36649 _36650).
Proof. exact (EQ_MP (@lem3470447 _89991 _36652 _36651 _36649 _36650) (@lem0)). Qed.
Lemma lem3470449 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : term829 _89991 _36652 _36651 _36649 _36650.
Proof. exact (EQ_MP (@lem3470448 _89991 _36652 _36651 _36649 _36650) (@lem3469040 _89991 _36651 _36652 _36649 _36650)). Qed.
Lemma lem3470451 (b : Prop) (a : Prop) : (a \/ b) = (term662 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3470452 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36650 : _89991) (_36651 : _89991 -> Prop) (_36652 : _89991) : (term829 _89991 _36652 _36651 _36649 _36650) = (term833 _89991 _36649 _36650 _36651 _36652).
Proof. exact (@lem3470451 (term834 _89991 _36652 _36651 _36649 _36650) (@I (_89991 -> Prop) _36651 _36652)). Qed.
Lemma lem3470454 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3470455 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term835 _89991 _36652 _36651 _36649 _36650) = (term836 _89991 _36652 _36651 _36649 _36650).
Proof. exact (@lem3470454 (term723 _89991 _36650 _36652) (term830 _89991 _36651 _36649 _36650)). Qed.
Lemma lem3470457 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470458 {_89991 : Type'} (_36650 : _89991) (_36652 : _89991) : (term735 _89991 _36650 _36652) = (_36650 = _36652).
Proof. exact (@lem3470457 (_36650 = _36652)). Qed.
Lemma lem3470459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470460 {_89991 : Type'} (_36650 : _89991) (_36652 : _89991) : (term736 _89991 _36650 _36652) = (term737 _89991 _36650 _36652).
Proof. exact (MK_COMB (@lem3470459) (@lem3470458 _89991 _36650 _36652)). Qed.
Lemma lem3470462 (a : Prop) (b : Prop) : (term731 a b) = (term732 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3470463 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term837 _89991 _36651 _36649 _36650) = (term838 _89991 _36651 _36649 _36650).
Proof. exact (@lem3470462 (term827 _89991 _36649 _36651) (term508 _89991 _36649 _36650)). Qed.
Lemma lem3470465 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470466 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36651 : _89991 -> Prop) : (term839 _89991 _36649 _36651) = (_36649 = _36651).
Proof. exact (@lem3470465 (_36649 = _36651)). Qed.
Lemma lem3470467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470468 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36651 : _89991 -> Prop) : (term840 _89991 _36649 _36651) = (term841 _89991 _36649 _36651).
Proof. exact (MK_COMB (@lem3470467) (@lem3470466 _89991 _36649 _36651)). Qed.
Lemma lem3470470 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3470471 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36650 : _89991) : (term794 _89991 _36649 _36650) = (@I (_89991 -> Prop) _36649 _36650).
Proof. exact (@lem3470470 (@I (_89991 -> Prop) _36649 _36650)). Qed.
Lemma lem3470472 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term838 _89991 _36651 _36649 _36650) = (term842 _89991 _36651 _36649 _36650).
Proof. exact (MK_COMB (@lem3470468 _89991 _36649 _36651) (@lem3470471 _89991 _36649 _36650)). Qed.
Lemma lem3470473 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term837 _89991 _36651 _36649 _36650) = (term842 _89991 _36651 _36649 _36650).
Proof. exact (TRANS (@lem3470463 _89991 _36651 _36649 _36650) (@lem3470472 _89991 _36651 _36649 _36650)). Qed.
Lemma lem3470474 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term836 _89991 _36652 _36651 _36649 _36650) = (term843 _89991 _36652 _36651 _36649 _36650).
Proof. exact (MK_COMB (@lem3470460 _89991 _36650 _36652) (@lem3470473 _89991 _36651 _36649 _36650)). Qed.
Lemma lem3470475 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term835 _89991 _36652 _36651 _36649 _36650) = (term843 _89991 _36652 _36651 _36649 _36650).
Proof. exact (TRANS (@lem3470455 _89991 _36652 _36651 _36649 _36650) (@lem3470474 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3470477 {_89991 : Type'} (_36652 : _89991) (_36651 : _89991 -> Prop) (_36649 : _89991 -> Prop) (_36650 : _89991) : (term844 _89991 _36652 _36651 _36649 _36650) = (term845 _89991 _36652 _36651 _36649 _36650).
Proof. exact (MK_COMB (@lem3470476) (@lem3470475 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470478 {_89991 : Type'} (_36651 : _89991 -> Prop) (_36652 : _89991) : (@I (_89991 -> Prop) _36651 _36652) = (@I (_89991 -> Prop) _36651 _36652).
Proof. exact (eq_refl (@I (_89991 -> Prop) _36651 _36652)). Qed.
Lemma lem3470479 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36650 : _89991) (_36651 : _89991 -> Prop) (_36652 : _89991) : (term833 _89991 _36649 _36650 _36651 _36652) = (term846 _89991 _36649 _36650 _36651 _36652).
Proof. exact (MK_COMB (@lem3470477 _89991 _36652 _36651 _36649 _36650) (@lem3470478 _89991 _36651 _36652)). Qed.
Lemma lem3470480 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36650 : _89991) (_36651 : _89991 -> Prop) (_36652 : _89991) : (term829 _89991 _36652 _36651 _36649 _36650) = (term846 _89991 _36649 _36650 _36651 _36652).
Proof. exact (TRANS (@lem3470452 _89991 _36649 _36650 _36651 _36652) (@lem3470479 _89991 _36649 _36650 _36651 _36652)). Qed.
Lemma lem3470482 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term847 _89991 t x''' x''''.
Proof. exact (conj (@lem3470292 _89991 t x''' x'''') (@lem3470335 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470483 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term848 _89991 t x''' x''''.
Proof. exact (conj (@lem3470283 _89991 _90000 t x x''' x'''' s f h1 h2) (@lem3470482 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470485 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36650 : _89991) (_36651 : _89991 -> Prop) (_36652 : _89991) : term846 _89991 _36649 _36650 _36651 _36652.
Proof. exact (EQ_MP (@lem3470480 _89991 _36649 _36650 _36651 _36652) (@lem3470449 _89991 _36652 _36651 _36649 _36650)). Qed.
Lemma lem3470486 {_89991 : Type'} (_36649 : _89991 -> Prop) (_36650 : _89991) (_36651 : _89991 -> Prop) (_36652 : _89991) : term846 _89991 _36649 _36650 _36651 _36652.
Proof. exact (@lem3470485 _89991 _36649 _36650 _36651 _36652). Qed.
Lemma lem3470487 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : term849 _89991 t x''' x''''.
Proof. exact (@lem3470486 _89991 (term713 _89991 t x''' x'''') (term815 _89991 t x''' x'''') (term713 _89991 t x''' x'''') (@I ((_89991 -> Prop) -> _89991) x''' x'''')). Qed.
Lemma lem3470490 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term850 _89991 t x''' x''''.
Proof. exact (@lem3470487 _89991 t x''' x'''' (@lem3470483 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470491 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term851 _89991 t x''' x''''.
Proof. exact (fun h0 : term852 _89991 t x''' x'''' => @lem3470490 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3470493 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470494 {_89991 : Type'} (t : type1402 _89991) (x''' : type684 _89991) (x'''' : _89991 -> Prop) : (term851 _89991 t x''' x'''') = (term850 _89991 t x''' x'''').
Proof. exact (@lem3470493 (term850 _89991 t x''' x'''')). Qed.
Lemma lem3470495 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term850 _89991 t x''' x''''.
Proof. exact (EQ_MP (@lem3470494 _89991 t x''' x'''') (@lem3470491 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470497 (a : Prop) (b : Prop) : (term669 a b) = (term670 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3470498 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) (_36623 : _89991) : (term648 _89991 _90000 x f t _36623) = (term853 _89991 _90000 x f t _36623).
Proof. exact (@lem3470497 (x = (@I (_89991 -> _90000) f _36623)) (term490 _89991 t _36623)). Qed.
Lemma lem3470500 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3470501 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) (_36623 : _89991) : (term853 _89991 _90000 x f t _36623) = (term854 _89991 _90000 x f t _36623).
Proof. exact (@lem3470500 (term855 _89991 _90000 x f t _36623)). Qed.
Lemma lem3470502 {_89991 _90000 : Type'} (x : _90000) (f : _89991 -> _90000) (t : type1402 _89991) (_36623 : _89991) : (term648 _89991 _90000 x f t _36623) = (term854 _89991 _90000 x f t _36623).
Proof. exact (TRANS (@lem3470498 _89991 _90000 x f t _36623) (@lem3470501 _89991 _90000 x f t _36623)). Qed.
Lemma lem3470504 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term856 _89991 _90000 x f t x''' x''''.
Proof. exact (conj (@lem3469182 _89991 _90000 t x x''' x'''' s f h1 h2) (@lem3470495 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470506 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term854 _89991 _90000 x f t _36623.
Proof. exact (EQ_MP (@lem3470502 _89991 _90000 x f t _36623) (@lem3468785 _89991 _90000 _36623 t s x f x''' h1)). Qed.
Lemma lem3470507 {_89991 _90000 : Type'} (_36623 : _89991) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term854 _89991 _90000 x f t _36623.
Proof. exact (@lem3470506 _89991 _90000 _36623 t s x f x''' h1). Qed.
Lemma lem3470508 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term506 _89991 _90000 t s x f x''') : term857 _89991 _90000 x f t x''' x''''.
Proof. exact (@lem3470507 _89991 _90000 (@I ((_89991 -> Prop) -> _89991) x''' x'''') t s x f x''' h1). Qed.
Lemma lem3470511 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : False.
Proof. exact (@lem3470508 _89991 _90000 x'''' t s x f x''' h1 (@lem3470504 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470512 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : term676.
Proof. exact (fun h0 : ~ False => @lem3470511 _89991 _90000 t x x''' x'''' s f h1 h2). Qed.
Lemma lem3470514 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3470515 : term676 = False.
Proof. exact (@lem3470514 False). Qed.
Lemma lem3470516 {_89991 _90000 : Type'} (t : type1402 _89991) (x : _90000) (x''' : type684 _89991) (x'''' : _89991 -> Prop) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term506 _89991 _90000 t s x f x''') (h2 : term474 _89991 _90000 x'''' s f) : False.
Proof. exact (EQ_MP (@lem3470515) (@lem3470512 _89991 _90000 t x x''' x'''' s f h1 h2)). Qed.
Lemma lem3470517 {_89991 _90000 : Type'} (x' : _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x'' : _89991 -> Prop) (h1 : term520 _89991 _90000 x' s x f x'') : False.
Proof. exact (EQ_MP (@lem3469020) (@lem3469017 _89991 _90000 x' s x f x'' h1)). Qed.
Lemma lem3470518 {_89991 _90000 : Type'} (x'''' : _89991 -> Prop) (x' : _89991) (x'' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term474 _89991 _90000 x'''' s f) (h2 : term464 _89991 _90000 x' x'' t s x f x''') : False.
Proof. exact (or_elim (@lem3468071 _89991 _90000 x' x'' t s x f x''' h2) (fun h0 : term520 _89991 _90000 x' s x f x'' => @lem3470517 _89991 _90000 x' s x f x'' h0) (fun h0 : term506 _89991 _90000 t s x f x''' => @lem3470516 _89991 _90000 t x x''' x'''' s f h0 h1)). Qed.
Lemma lem3470519 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (t : type1402 _89991) (s : type686 _89991) (x : _90000) (f : _89991 -> _90000) (x''' : type684 _89991) (h1 : term80 _89991 _90000 s f) (h2 : term464 _89991 _90000 x' x'' t s x f x''') : False.
Proof. exact (ex_elim (@lem3467109 _89991 _90000 s f h1) (fun x'''' : _89991 -> Prop => fun h0 : term858 _89991 _90000 s f x'''' => @lem3470518 _89991 _90000 x'''' x' x'' t s x f x''' h0 h2)). Qed.
Lemma lem3470520 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (t : type1402 _89991) (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term467 _89991 _90000 x' x'' t s x f) (h2 : term80 _89991 _90000 s f) : False.
Proof. exact (ex_elim (@lem3467871 _89991 _90000 x' x'' t s x f h1) (fun x''' : type684 _89991 => fun h0 : term466 _89991 _90000 x' x'' t s x f x''' => @lem3470519 _89991 _90000 x' x'' t s x f x''' h2 h0)). Qed.
Lemma lem3470521 {_89991 _90000 : Type'} (x' : _89991) (x'' : _89991 -> Prop) (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term469 _89991 _90000 x' x'' s x f) (h2 : term80 _89991 _90000 s f) : False.
Proof. exact (ex_elim (@lem3467870 _89991 _90000 x' x'' s x f h1) (fun t : type1402 _89991 => fun h0 : term468 _89991 _90000 x' x'' s x f t => @lem3470520 _89991 _90000 x' x'' t x s f h0 h2)). Qed.
Lemma lem3470522 {_89991 _90000 : Type'} (x' : _89991) (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term471 _89991 _90000 x' s x f) (h2 : term80 _89991 _90000 s f) : False.
Proof. exact (ex_elim (@lem3467869 _89991 _90000 x' s x f h1) (fun x'' : _89991 -> Prop => fun h0 : term470 _89991 _90000 x' s x f x'' => @lem3470521 _89991 _90000 x' x'' x s f h0 h2)). Qed.
Lemma lem3470523 {_89991 _90000 : Type'} (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term149 _89991 _90000 s x f) (h2 : term80 _89991 _90000 s f) : False.
Proof. exact (ex_elim (@lem3467868 _89991 _90000 s x f h1) (fun x' : _89991 => fun h0 : term472 _89991 _90000 s x f x' => @lem3470522 _89991 _90000 x' x s f h0 h2)). Qed.
Lemma lem3470524 {_89991 _90000 : Type'} (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term149 _89991 _90000 s x f) (h2 : term80 _89991 _90000 s f) : (term149 _89991 _90000 s x f) = False.
Proof. exact (prop_ext (fun h3 : term149 _89991 _90000 s x f => @lem3470523 _89991 _90000 x s f h1 h2) (fun h3 : False => @lem3466876 _89991 _90000 s x f h1)). Qed.
Lemma lem3470525 {_89991 _90000 : Type'} (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term149 _89991 _90000 s x f) (h2 : term80 _89991 _90000 s f) : False.
Proof. exact (EQ_MP (@lem3470524 _89991 _90000 x s f h1 h2) (@lem3466876 _89991 _90000 s x f h1)). Qed.
Lemma lem3470526 {_89991 _90000 : Type'} (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term80 _89991 _90000 s f) : term148 _89991 _90000 s x f.
Proof. exact (fun h0 : term149 _89991 _90000 s x f => @lem3470525 _89991 _90000 x s f h0 h1). Qed.
Lemma lem3470527 {_89991 _90000 : Type'} (x : _90000) (s : type686 _89991) (f : _89991 -> _90000) (h1 : term80 _89991 _90000 s f) : (term100 _89991 _90000 x f s) = (term131 _89991 _90000 s x f).
Proof. exact (EQ_MP (@lem3466875 _89991 _90000 s x f) (@lem3470526 _89991 _90000 x s f h1)). Qed.
Lemma lem3470532 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) (h1 : term80 _89991 _90000 s f) : term134 _89991 _90000 s f.
Proof. exact (fun x : _90000 => @lem3470527 _89991 _90000 x s f h1). Qed.
Lemma lem3470533 {_89991 _90000 : Type'} (s : type686 _89991) (f : _89991 -> _90000) : term135 _89991 _90000 s f.
Proof. exact (fun h0 : term80 _89991 _90000 s f => @lem3470532 _89991 _90000 s f h0). Qed.
Lemma lem3470538 {_89991 _90000 : Type'} (f : _89991 -> _90000) : term137 _89991 _90000 f.
Proof. exact (fun s : type686 _89991 => @lem3470533 _89991 _90000 s f). Qed.
Lemma lem3470543 {_89991 _90000 : Type'} : term139 _89991 _90000.
Proof. exact (fun f : _89991 -> _90000 => @lem3470538 _89991 _90000 f). Qed.
Lemma lem3470544 {_89991 _90000 : Type'} : term141 _89991 _90000.
Proof. exact (EQ_MP (@lem3466870 _89991 _90000) (@lem3470543 _89991 _90000)). Qed.
Lemma lem3470546 {_89991 _90000 : Type'} : term141 _89991 _90000.
Proof. exact (@lem3466482 _89991 _90000 (@lem3470544 _89991 _90000)). Qed.
Lemma lem3470547 {_89991 _90000 : Type'} (h1 : term142 _89991 _90000) : False.
Proof. exact (@lem3470546 _89991 _90000 (@lem3466466 _89991 _90000 h1)). Qed.
Lemma lem3470548 {_89991 _90000 : Type'} (h1 : term142 _89991 _90000) : (term142 _89991 _90000) = False.
Proof. exact (prop_ext (fun h2 : term142 _89991 _90000 => @lem3470547 _89991 _90000 h1) (fun h2 : False => @lem3466466 _89991 _90000 h1)). Qed.
Lemma lem3470549 {_89991 _90000 : Type'} (h1 : term142 _89991 _90000) : False.
Proof. exact (EQ_MP (@lem3470548 _89991 _90000 h1) (@lem3466466 _89991 _90000 h1)). Qed.
Lemma lem3470550 {_89991 _90000 : Type'} : term141 _89991 _90000.
Proof. exact (fun h0 : term142 _89991 _90000 => @lem3470549 _89991 _90000 h0). Qed.
Lemma lem3470551 {_89991 _90000 : Type'} : term139 _89991 _90000.
Proof. exact (EQ_MP (@lem3466465 _89991 _90000) (@lem3470550 _89991 _90000)). Qed.
Lemma lem3470552 {_89991 _90000 : Type'} : term45 _89991 _90000.
Proof. exact (EQ_MP (@lem3466461 _89991 _90000) (@lem3470551 _89991 _90000)). Qed.
Lemma lem3470553 {_89991 _90000 : Type'} : term28 _89991 _90000.
Proof. exact (EQ_MP (@lem3466140 _89991 _90000) (@lem3470552 _89991 _90000)). Qed.
Lemma lem3470554 {_89991 _90000 : Type'} : term27 _89991 _90000.
Proof. exact (EQ_MP (@lem3466040 _89991 _90000) (@lem3470553 _89991 _90000)). Qed.
