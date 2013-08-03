(ns solitaire.core
  (require clojure.edn))

(defmethod print-method clojure.lang.PersistentQueue [q w] (print-method '<- w) (print-method (seq q) w) (print-method '-< w))

(def red #{:hearts :diamonds :d :h})

(defn red? [suit] (boolean (red suit)))

(def black? (complement red?))

(defn named [i]
  (if (nil? i)
    "empty space"
    (-> i name clojure.string/capitalize)))

(defn to-s [[rank suit]]
  (->> [(if (nil? rank) "an" "the") ({11 "Jack" 12 "Queen" 13 "King" 1 "Ace"} rank rank)
        (if-not (nil? rank) "of") ({:h "Hearts" :d "Diamonds" :s "Spades" :c "Clubs"} suit (named suit))]
       (remove nil?)
       (clojure.string/join " ")))

(defn card-range
  ([suit end] (card-range suit 1 end))
  ([suit] (card-range suit 13))
  ([suit begin end]
     (->> (range begin (inc end))
          (map #(vector % suit))
          vec)))

(defn peek-pop
  ([stack]
     [(peek stack) (if (seq stack) (pop stack))])
  ([stack n]
     (loop [x n
            result [[] stack]]
       (let [[_ stack] result]
         (if-let [next-item (and (> x 0) (peek stack))]
           (recur (dec x)
                  (-> result
                      (update-in [0] conj next-item)
                      (update-in [1] pop)))
           result)))))

(defn normalize [{:keys [waste foundation tableau]}]
  "Internal representation:
     :f Foundation: up to four sequences of cards
     :tableau a sequence of maps: {:h index of next hidden :i index (refers to which stack of hidden cards) :s stack}
     :w Waste: a stack of cards
     :s Stock: a queue of cards
   Extra:
     :h Hidden Tableau: a sequence of up to seven (possibly nil) sequences of cards (possibly nil). Can
          be queried for cards, and remembered so that the user doens't need to repeatedly input the same
          card(s). The parameterized value in the state describes how the down-stacks are initalized."
  {:foundation (map (fn [[rank suit]] (card-range suit rank)) foundation)
   :tableau (into tableau (repeat (- 7 (count tableau)) []))})
;;  either make sure foundation always has count of 4 or check for count of 4 in winning?

(letfn [(move-type [& defns]
          (fn [state]
            (for [[source source-pred destination-pred] defns
                  [moving without-mover] (source-filter source-pred state)
                  accept-mover (find-destinations destination-pred moving state)]
              (-> state without-mover accept-mover))))
        (source-filter [pred source]
          (->> source
               (filter pred)
               (map #(let [{:keys [index]} %]
                       [(get-in state [:tableau index :stack])
                        (apply-update [:tableau index :stack] empty)]))))
        (orphan [{[[rank]] :stack}] (and rank (not= 13 rank)))
        (orphan-parent [[top-card] tableau]
          (filter (parent? top-card) tableau))
        (obscuring-king [{[[rank]] :stack hidden-index :hidden}]
          (and (= rank 13) (> hidden-index 0)))
        (empty-tableau [_ tableau]
          (->> tableau
               (remove #(seq (:stack %)))
               (take 1)))
        (card
          ([]
             #(peek %))
          ([fun]
             #(-> % fun peek))) 
        (to-foundation [{:keys [foundation]}]
          )
        (find-destinations [pred moving {:keys [tableau] :as state}]
          (->> tableau
               (pred moving)
               (map #(let [{:keys [index]} %]
                       (apply-update [:tableau index :stack] into moving)))))
        (parent? [[rank suit]]
          (fn [{parent-stack :stack}]
            (let [[parent-rank parent-suit] (peek parent-stack)]
              (and (= (red? parent-suit) (black? suit))
                   (= parent-rank (inc rank))))))
        (apply-update [keys & args]
          #(apply update-in % keys args))
        (stock-to-waste [state]
          (let [[new-waste new-stock] (-> state :stock (peek-pop 3))]
            (if (seq new-waste)
              (-> state
                  (update-in [:waste] into new-waste)
                  (assoc-in [:stock] new-stock))
              (if-let [waste (-> state :waste seq)]
                (-> state
                    (update-in [:stock] into waste)
                    (assoc-in [:waste] [])
                    recur)))))]
  (defn find-moves [{:keys [tableau] :as state}]
    (let [moves (;apply
                 move-type
                       [orphan orphan-parent]
                       [obscuring-king empty-tableau]
                       [:tableau (card :stack) to-foundation]
                    ;   (map #(vector pop % to-tableau) [waste-card foundation-card])
                       )]
      (conj (moves state)
            (stock-to-waste state)))))

(defn solve
  "Takes a state (including a sequence of previous states) plus a description of the current move; returns a sequence of moves or nil.
  Keys: t (tableau) sequence of seven cards, the initial showing ones (or a sequence of card sequences, if partially played)
        f (foundation) optional; sequence of four cards, the top ones showing
        w (waste) optional (defaults to empty); a sequence of cards
        s (stock) sequence of cards in the stock, nil for unknown
   ** A card is a sequence of rank, suit; where rank: int (0, 13) inclusive, suit: #{:c :d :h :s}
      e.g. [12 :s] -> Queen of Spades
   Jack -> 11
   Queen -> 12
   King -> 13
   Ace -> 1"
  [initial-state]
  (letfn [(add-layouts [previous state]
            (conj previous (without-history state)))
          (without-history [state]
            (select-keys state [:foundation :tableau :hidden :stock :waste]))
          (winning? [state]
            (if (every? #(= 13 (count %)) (state :foundation))
              (state :history)))
          (in? [previous]
            (fn [state] (previous (without-history state))))]
    (loop [moves (normalize initial-state)
           previous-layouts #{}]
      (if-let [winning-moves (some winning? moves)]
        winning-moves
        (if (seq moves)
          (let [uninteresting? (some-fn nil? (in? previous-layouts))  ; might not need to check for nil here (flatten nil) -> ()
                next-moves (->> moves
                                (mapcat find-moves)
                                (remove uninteresting?))]
            (recur next-moves (reduce add-layouts previous-layouts next-moves))))))))
