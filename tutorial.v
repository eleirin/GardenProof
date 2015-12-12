
(** Yooooosh! Avec un peu de retard, voici mon petit tutoriel sur SSReflect.
* Je t'y partage un peu de tout ce que j'ai appris, en esperant que ce ne soit pas trop confus et assez ordone
* Donc commencons sans plus attendre ^^ *)

Require Export ssreflect.
Require Import ssrnat.
Require Import ssrbool.
Require Import ssrfun.
Require Import seq.
Require Import Permutation.
Require Import eqtype.
(*TODO: Reecrire les bibliotheques dans le bon ordre*)

(****** La gestion de la stack *****)
(** Comme je t'expliquais, SSReflect permet de manipuler la stack de facon tres fluide. Prenons par exemple: *)

Lemma Test_move_stack A B C: (A -> B -> C) -> (A -> B) -> A -> C.
move => Habc Hab Ha.
(** On voit la notre premier symbole chelou. => permet de poper de la stack de preuve un objet*)
move : Habc.
(** Et voici notre second. : lui push un objet sur la stack. Bien entendu on peut les combiner: *)
move : Hab => Hba.
(** A ton avis que c'est il passe? Vi, on a renomme Hab en Hba. En gros, l'ordre a retenir pour l'instant c'est que : arrive avant la tactique et => apres. Ca veut notamment dire qu'on ne peut pas ecrire cela:
* move => Hba : Ha.
* Car l'ordre ne serait pas respecte. Cette question d'ordre assure une certaine coherence en SSReflect ainsi que des lignes de codes relativement courtes.*)
apply.
(** Voila une seconde tactique. Apply prend l'hypothese du haut de la pile et essaie de l'appliquer au but. Presque toute les tactiques de SSR ne prennent pas d'argument et fonctionne plutot sur l'hyppothese en debut de pile *) 
apply: Ha.
apply: Hba.
apply: Ha.
Qed.

(*Bien sur, on aurait pu combiner le tout et donner une version de la preuve plus fluide:*)
Lemma Test2 A B C: (A -> B -> C) -> (A -> B) -> A -> C.
move => Habc Hab Ha.
apply: (Habc Ha (Hab Ha)).
Qed.

(*En fait, plutot que apply, on aurait plus utiliser exact. Exact est ce qu'on appelle un terminateur. Ce sont certaines tactiques comme done et by qui  finissent la preuve. C'est une bonne pratique d'utiliser ceux ci en fin de preuve*)

(*Lemma Test_final A B C: (A

apply: Habc.
apply: Ha.

pply: Hab.
apply: Ha.
Qed.*)

(* Tu t'en doutes, cette façon de proceder est assez fastidieuse. En fait, ce genre de tactique peut bient *)

Section ABR.
        Variable T: eqType.
        Hypotheses (R: rel T).
                   (* (R_trans: transitive R)
                      (R_total: total R)
                      (R_antisym: antisymmetric R).*)
                   
Inductive Arbre : Type :=
|Leaf
|Node of T & Arbre & Arbre.

Inductive in_Arbre (a: T) (arb: Arbre) : Prop:=
|in_now l r of arb = Node a l r
|in_left b l r of arb = Node b l r & in_Arbre a l
|in_right b l r of arb = Node b l r & in_Arbre a r.
Implicit Arguments in_now [a arb].

Implicit Arguments in_right [a arb].

Fixpoint naive_in_b (a: T) (arb : Arbre) := match arb with
|Leaf => false
|Node b l r =>  (b == a) || naive_in_b a l || naive_in_b a r
end.

Lemma naive_in_bP arb a: reflect (in_Arbre a arb) (naive_in_b a arb).
elim: arb; 
    first by apply: ReflectF; case.
move => s l HreflectL r HreflectR.
rewrite /naive_in_b -/naive_in_b.
case eqas: (s == a).
    by move /eqP : eqas <-; apply: ReflectT; apply (in_now l r).
case inl : (naive_in_b a l) => /=.
    by apply: ReflectT; apply: (in_left s l r) => //; apply /HreflectL : inl.
case inr : (naive_in_b a r) => /=.
    by apply: ReflectT; apply: (in_right s l r) => //; apply /HreflectR : inr.
apply: ReflectF.
case.
    by move /eqP: eqas; move => eqas _ _ [] //.
    by move /HreflectL: inl; move => inl _ _ _ [_ <- _] //.
    by move /HreflectR: inr; move => inr _ _ _ [_ _ <-] //.
Qed.

Inductive ABR (arb: Arbre) :Prop := 
|ABR_intro s l r of arb = Node s l r & ABR l & ABR r & 
                   (forall a, in_Arbre a l -> R a s) & 
                   (forall b, in_Arbre b r -> ~~(R b s)).

Definition singleton a := Node a Leaf Leaf.

Inductive insert_at_leaf a arb res : Prop :=
|insert_leaf of arb = Leaf & res = singleton a

Inductive in_Arbre (a: T) (arb: Arbre) : Prop:=
|in_now l r of arb = Node a l r
|in_left b l r of arb = Node b l r & in_Arbre a l
|in_right b l r of arb = Node b l r & in_Arbre a r.
Implicit Arguments in_now [a arb].
Implicit Arguments in_right [a arb].

Fixpoint naive_in_b (a: T) (arb : Arbre) := match arb with
|Leaf => false
|Node b l r =>  (b == a) || naive_in_b a l || naive_in_b a r
end.

Lemma naive_in_bP arb a: reflect (in_Arbre a arb) (naive_in_b a arb).
elim: arb; 
    first by apply: ReflectF; case.
move => s l HreflectL r HreflectR.
rewrite /naive_in_b -/naive_in_b.
case eqas: (s == a).
    by move /eqP : eqas <-; apply: ReflectT; apply (in_now l r).
case inl : (naive_in_b a l) => /=.
    by apply: ReflectT; apply: (in_left s l r) => //; apply /HreflectL : inl.
case inr : (naive_in_b a r) => /=.
    by apply: ReflectT; apply: (in_right s l r) => //; apply /HreflectR : inr.
apply: ReflectF.
case.
    by move /eqP: eqas; move => eqas _ _ [] //.
    by move /HreflectL: inl; move => inl _ _ _ [_ <- _] //.
    by move /HreflectR: inr; move => inr _ _ _ [_ _ <-] //.
Qed.

Inductive ABR (arb: Arbre) :Prop := 
|ABR_intro s l r of arb = Node s l r & ABR l & ABR r & 
                   (forall a, in_Arbre a l -> R a s) & 
                   (forall b, in_Arbre b r -> ~~(R b s)).

Definition singleton a := Node a Leaf Leaf.

Inductive insert_at_leaf a arb res : Prop :=
|insert_leaf of arb = Leaf & res = singleton a
|insert_left b r of arb = Node b Leaf r & res = Node b (singleton a) r
|insert_right b l of arb = Node b l Leaf & res = Node b l (singleton a). 
Implicit Arguments insert_leaf [a arb res].
Implicit Arguments insert_left [a arb res].
Implicit Arguments insert_right [a arb res].

Lemma ABR_left a l r : ABR (Node a l r) -> ABR l.
by move => [] _ _ _ [] <- <- <-.
Qed.
Lemma ABR_right a l r: ABR (Node a l r) -> ABR r.
by move => [] _ _ _ [] <- <- <-.
Qed.
Program Fixpoint insert a arb (h: ABR arb): {res | insert_at_leaf a arb res /\ ABR res}
                := match arb with
|Leaf => Node a Leaf Leaf
|Node b l r => if (R a b) then Node b (insert a l (ABR_left b l r h)) r else Node b l (insert a r (ABR_right b l r h))
                end.
Proof.
        Next Obligation.
split.
by apply: insert_leaf.
exists a Leaf Leaf => //.
by move => ? [].
by move => ? [].
Qed.
    Next Obligation.
split.
case: (R a b).
case: i0 => [-> ->| |].
by apply: (insert_left b r).
move => ? ? -> ->.
by apply: (insert_
done.


Inductive in_ABR a (arb: Arbre): Prop :=
|in_ABR_now l r of arb = Node a l r
|in_ABR_left b l r of arb = Node b l r & R a b & in_ABR a l
|in_ABR_right b l r of arb = Node b l r & ~~(R a b) & in_ABR a r.
Implicit Arguments in_ABR_now [a arb].
Implicit Arguments in_ABR_left [a arb].
Implicit Arguments in_ABR_right [a arb].



Lemma in_ABR_in_equiv (arb: Arbre) a : ABR arb -> (in_ABR a arb <-> in_Arbre a arb).
move => HARB.
split.

- elim. 
      by move => _ l r ->; apply: (in_now l r).
      by move => _ b l r -> _ _; apply: (in_left b l r).
      by move => _ b l r -> _ _; apply: (in_right b l r).


- move => Hin.
  elim: Hin HARB.
      by move => _ l r -> _; apply (in_ABR_now l r).
  move => _ b l r -> HinArbre HinABR.
  move => [] // _ _ _ [] <- <- <- HABRl _ Hinf _.
  apply: (in_ABR_left b l r) => //. 
      by apply: Hinf => //.
      by apply: HinABR.
  move => _ b l r -> HinArbre HinABR.
  move => [] // _ _ _ [] <- <- <- _ HABRr _ Hsup.
  apply: (in_ABR_right b l r) => //. 
      by apply: Hsup => //.
      by apply: HinABR.
Qed. 

Fixpoint in_b_abr a arb := match arb with
|Leaf => false
|Node b l r => (b == a) || (if R a b then in_b_abr a l else in_b_abr a r)
end.

Lemma in_b_abr_P a arb : reflect (in_ABR a arb) (in_b_abr a arb).
elim: arb.
    by apply: ReflectF; case.
move => s l HrefL r HrefR.
rewrite /in_b_abr -/in_b_abr.
case eqas: (s == a).
    by move /eqP : eqas <-; apply: ReflectT; apply (in_ABR_now l r).
case Ras: (R a s).
case inl: (in_b_abr a l).
    apply: ReflectT.
    apply: (in_ABR_left s l r) => //; apply /HrefL : inl.
    apply: ReflectF.
    case.
|xor_gt of n > m : xor_le_gt n m false true.

Lemma xor_P n m: xor_le_gt n m (n <= m) (n > m).
Proof.
        rewrite ltnNge.
case X : (n <= m).
  + constructor => //.
  + constructor by rewrite ltnNge X.
Qed.

Lemma not_le_gt n m: (n <= m) -> (n > m) -> False.
by case: xor_P.
move => Hnm Hmn.
move : (conj Hnm Hmn).
move /andP.
by case: xor_P.
Qed.

Section Perm.
Variable T: eqType.

Fixpoint Occurence a (l: seq T) := if l is b::l' then ((a == b) + Occurence a l') else O.

Lemma Occurence_cons a l : Occurence a (a :: l) = (Occurence a l) .+1.
Proof. by rewrite /Occurence eq_refl. Qed.
Lemma Occurence_ignore b l a: (a == b) = false -> Occurence a (b :: l) = Occurence a l.
Proof. by move => /= ->. Qed.


Definition Permutation_Occ l l' := nosimpl (forall a, Occurence a l = Occurence a l').

Lemma PO_sym l l' : Permutation_Occ l l' -> Permutation_Occ l' l.
Proof. by move => PO z. Qed.

Lemma PO_cons a l l': Permutation_Occ (a::l) (a::l') -> Permutation_Occ l l'.
Proof.
move => PO z.
move /(_ z) : PO.
rewrite !/Occurence.
case (z == a); [by move => [] | done].
Qed.

Lemma PO_nil l : Permutation_Occ nil l -> l = nil.
Proof.
case: l.
    done.
move => a ? /(_ a) /=.
by rewrite eq_refl.
Qed.

Lemma PO_singleton a l : Permutation_Occ [::a] l -> l = [::a].
Proof.
case: l => [/PO_sym /PO_nil | b l].
    done.
case X : (b == a).
    by move /eqP : X => -> /PO_cons /PO_nil ->.
move / (_ b).
rewrite Occurence_cons Occurence_ignore => //.
Qed.

Fixpoint insert_at (a: T) n s := match n, s with
|S m, b::s' => b :: (insert_at a m s')
|_, _ => a::s
end.

Lemma insert_nil a n : insert_at a n [::] = [:: a].
Proof. by case : n. Qed.
Lemma insert_zero a l : insert_at a 0 l = a :: l.
Proof. done. Qed.
Lemma insert_cons a n b l : insert_at a n.+1 (b::l) = b::(insert_at a n l).
Proof. done. Qed.

Lemma Occurence_insert_cons a l n: (Occurence a (insert_at a n l)) = (Occurence a l) .+1.
Proof.
elim: n a l => [| n Hrec] a l.
    by rewrite Occurence_cons.
case: l => [| b l] /=.
    by rewrite eq_refl.
    by rewrite Hrec.
Qed.

Lemma Occurence_insert_ignore a l n z: (z == a) = false -> (Occurence z (insert_at a n l)) = Occurence z l.
elim: n a l z => [|n Hrec] a l z.
    by move => /= ->.
case: l => [/= -> | b l Hneq /=].
    done.
by rewrite Hrec.
Qed.


Lemma Permutation_insert_swap n a l: Permutation (insert_at a n l) (insert_at a n.+1l).
Proof.
elim: n a l => [| m Hrec] a l.
    case: l => *.
        by rewrite !insert_nil; exact: Permutation_refl.
        exact: perm_swap.
case: l => [|b l].
    by rewrite !insert_nil; exact: Permutation_refl.
rewrite !insert_cons.
apply: perm_skip.
apply: Hrec.
Qed.

Lemma Permutation_insert_double n m a l : Permutation (insert_at a n l) (insert_at a m l).
Proof.
wlog : n m /(n <= m).
    by case: (leqP n m) => [| /ltnW] X /(_ _ _ X) => //; exact: Permutation_sym.
move => /leP Hle.
elim: Hle a l => [|m' Hle Hrec] a l. 
    exact: Permutation_refl.
apply: (Permutation_trans (Hrec _ _)).
exact: Permutation_insert_swap.
Qed.

Lemma Permutation_insert_head a n l l': Permutation l l' -> Permutation (a::l) (insert_at a n l').
Proof.
elim: n l l' a => [| m Hrec] l l' a PO.
    exact : perm_skip.
case: l' PO => [/Permutation_sym /Permutation_nil -> | b l' PO].
    by rewrite insert_nil; exact: Permutation_refl.
apply: (Permutation_trans (Hrec _ (b :: l') _ _)) => //.
exact: Permutation_insert_double.
Qed.

Lemma PO_insert_inv a n l l' : Permutation_Occ (a::l) (insert_at a n l') -> Permutation_Occ l l'.
Proof.
move => PO z.
case X: (z == a); last first.
    by rewrite -(Occurence_ignore a _ _ X) -(Occurence_insert_ignore a l' n) => //. 
move : X => /eqP ->.
apply /eq_add_S.
rewrite -(Occurence_insert_cons a l' n) -Occurence_cons.
exact: PO.
Qed.

CoInductive insert_spec a : seq T -> Type :=
    insert_spec_intro l n: insert_spec a (insert_at a n l).

Lemma extract_insert a: forall l, 0 < Occurence a l -> insert_spec a l.
Proof.
elim => [| b l Hrec] Hocc.
    done.
case X: (a == b).
    by move : X => /eqP ->; rewrite -insert_zero; split.
move: Hrec => [|l' n].
    by rewrite -(Occurence_ignore b).
rewrite -insert_cons.
by split.
Qed.

Inductive insert_permutation: seq T -> seq T -> Type :=
|Perm_nil : insert_permutation nil nil
|Perm_add a n l l' of insert_permutation l l' : insert_permutation (a::l) (insert_at a n l').

Lemma Extract_perm: forall l l', Permutation_Occ l l' -> insert_permutation l l'.
Proof.
elim => [_ /PO_nil -> | a l Hrec l' PO].
     exact: Perm_nil.
move:(extract_insert a l') (PO) => [|tl' n POtl'].
    by move : PO => /(_ a) /= <-; rewrite eq_refl.
apply: Perm_add.
apply: Hrec.
exact: (PO_insert_inv a n).
Qed.

Lemma Instanciate_perm l l' : insert_permutation l l' -> Permutation l l'.
elim => *.
    by exact: perm_nil.
    by exact: Permutation_insert_head.
Qed.

Lemma Permutation_Occ_Permutation l l': Permutation_Occ l l' -> Permutation l l'.
Proof.
move => /(Extract_perm).
exact: Instanciate_perm.
Qed.

Lemma Permutation_Permutation_Occ l l': Permutation l l' -> Permutation_Occ l l'.
Proof.
elim => [| x l_ l_' _ PO /=| x y l_| l_ l_' l_'' _ eq1 _ eq2] z /=.
    done.
    by move : PO => /(_ z) ->.
    by ring.
    by move : eq1 eq2 => /(_ z) eq1 /(_ z) eq2; transitivity (Occurence z l_').
Qed.

Lemma Permutation_equiv l l' : Permutation l l' <-> Permutation_Occ l l'.
split.
    exact: Permutation_Permutation_Occ.
    exact: Permutation_Occ_Permutation.
Qed.

