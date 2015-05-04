#define NORTH 0
#define EAST 1
#define SOUTH 2
#define WEST 3

#define OFF_BOARD -1
#define BOARD_SIZE 3
#define CENTER (BOARD_SIZE / 2)
#define MAX_MOVE 5
#define NUM_PENGUINS 4

#define EARMUFFS 0
#define SNOWSHOES 1
#define SLINGSHOT 2
#define NUM_CARDS 3

#define INFINITY 10

typedef Point {
	short x;
	short y;
}

typedef Penguin {
	Point curr_pos;
	byte dir;
	short health;
	byte points;
	Point home;
	bool stunned;
	bool has_snowball;
	bool has_card[NUM_CARDS];
	bool using_card[NUM_CARDS];
    bool has_used_card[NUM_CARDS];
}

Penguin penguins[NUM_PENGUINS];
bool game_over = false;
bool ltl_okay = false;


inline move() {
	int i;
	int move_dists[NUM_PENGUINS];
	int snowshoe_dirs[NUM_PENGUINS];
	for (i in move_dists) {
		int j;
		select (j : 0 .. MAX_MOVE);
		move_dists[i] = j;
		select (j : NORTH .. WEST);
		snowshoe_dirs[i] = j;	
	}

	skip;
	d_step {
		for (i in penguins) {
			if
			:: !penguins[i].stunned ->
				max_move_dist(penguins[i], move_dists[i]);
				move_penguin(penguins[i], move_dists[i]);
				printf("Penguin %d moved %d spaces to (%d, %d)\n", 
				       i, move_dists[i], penguins[i].curr_pos.x, 
				       penguins[i].curr_pos.y);
				assert(!(penguins[i].curr_pos.x == CENTER &&
				         penguins[i].curr_pos.y == CENTER));
			:: else
			fi;
		}
	
		for (i in penguins) {
			if
			:: penguins[i].using_card[SNOWSHOES] ->
				int dir = snowshoe_dirs[i];
				bool in_bounds;
				Point next_pos;
				do
				::
					relocate(next_pos, penguins[i].curr_pos);
					if
					:: dir == NORTH ->
						next_pos.y--;
					:: dir == EAST  ->
						next_pos.x++;
					:: dir == SOUTH ->
						next_pos.y++;
					:: dir == WEST  ->
						next_pos.x--;
					fi;
					check_in_bounds(next_pos, in_bounds);
					if
					:: in_bounds ->
						relocate(penguins[i].curr_pos, next_pos);
						break;
					:: else ->
						dir = (dir + 1) % 4
					fi;
				od;
				penguins[i].using_card[SNOWSHOES] = false;
                penguins[i].has_used_card[SNOWSHOES] = true;
			:: else
			fi;
		}
		check_collisions()
	}
	
}

inline max_move_dist(p, dist) {
	if
	:: p.dir == NORTH ->
		min(p.curr_pos.y, dist, dist);
	:: p.dir == EAST  ->
		min((BOARD_SIZE - p.curr_pos.x), dist, dist);
	:: p.dir == SOUTH ->
		min((BOARD_SIZE - p.curr_pos.y), dist, dist);
	:: p.dir == WEST  ->
		min(p.curr_pos.x, dist, dist);
	fi;
}

inline min(a, b, ret) {
	if 
	:: a < b -> ret = a;
	:: else  -> ret = b;
	fi;
}

inline move_penguin(p, dist) {
	if
	:: p.dir == NORTH -> 
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y > CENTER && 
		   p.curr_pos.y - dist < CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y - dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.y = p.curr_pos.y - dist;
	:: p.dir == EAST  -> 
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x < CENTER && 
		   p.curr_pos.x + dist > CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x + dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.x = p.curr_pos.x + dist;
	:: p.dir == SOUTH -> 
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y < CENTER && 
		   p.curr_pos.y + dist > CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y + dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.y = p.curr_pos.y + dist;
	:: p.dir == WEST  -> 
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x > CENTER && 
		   p.curr_pos.x - dist < CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x - dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.x = p.curr_pos.x - dist;
	fi; 
}

inline check_collisions() {
	int m;
	for (m in penguins){
		int n;
		for (n in penguins){
			bool collision;
			check_collision(penguins[m].curr_pos, penguins[n].curr_pos, collision)
			if
			:: collision && m > n ->
				penguins[m].health--;
				penguins[m].has_snowball = false;
				penguins[n].health--;
				penguins[n].has_snowball = false;
			:: else
			fi;
		}
	}
	stun_only_cleanup()
}


inline shoot() {
	int i;
	int shoot_dirs[NUM_PENGUINS];
	for (i in penguins){
		int dir;
		select (dir : NORTH .. WEST);
		shoot_dirs[i] = dir;
	}
	skip;
	d_step {
		for (i in penguins){
			if
			:: penguins[i].has_snowball ->
				Point snowball;
				snowball.x = penguins[i].curr_pos.x;
				snowball.y = penguins[i].curr_pos.y;
				penguins[i].has_snowball = false;
				bool in_bounds;
				bool penguin_hit = false;
				do ::
					if
					:: penguins[i].using_card[SLINGSHOT] ->
						move_snowball_diag(snowball, shoot_dirs[i]);
					:: else ->
						move_snowball(snowball, shoot_dirs[i]);
					fi;
					check_in_bounds(snowball, in_bounds);
					if
					:: !in_bounds || penguin_hit -> break;
					:: else -> 
						int j;
						for (j in penguins) {	
							bool collision;
							check_collision(snowball, penguins[j].curr_pos, collision)
							if
							:: collision && !penguins[j].stunned -> 
								penguins[i].points++;
								penguins[j].health--;
								penguin_hit = true;
							:: else
							fi;
						}
					fi;
				od;
                if
                :: penguins[i].using_card[SLINGSHOT] ->
				    penguins[i].using_card[SLINGSHOT] = false;
                    penguins[i].has_used_card[SLINGSHOT] = true;
                :: else
                fi;
			:: else
			fi
		}
	}
}

inline move_snowball(s, dir){
	if
	:: dir == NORTH ->
		s.y--;
	:: dir == SOUTH ->
		s.y++;
	:: dir == EAST  ->
		s.x++;
	:: dir == WEST  ->
		s.x--;
	fi;
}

inline move_snowball_diag(s, dir){
	if
	:: dir == NORTH ->
		s.y--;
		s.x++;
	:: dir == SOUTH ->
		s.y++;
		s.x--;
	:: dir == EAST  ->
		s.x++;
		s.y++;
	:: dir == WEST  ->
		s.x--;
		s.y--;
	fi;
}

inline check_in_bounds(s, ret){
	ret = s.x >= 0 && s.x < BOARD_SIZE && s.y >= 0 && s.y < BOARD_SIZE &&
	      (s.x != CENTER || s.y != CENTER);
}

inline check_collision(p1, p2, ret){
	ret = p1.x == p2.x && p1.y == p2.y;
}

inline turn() {
	int i;
	int turn_dirs[NUM_PENGUINS];
	for (i in penguins){ 
		int dir;
		select (dir : NORTH .. WEST);
		turn_dirs[i] = dir;
	}
	skip;
	d_step {
		for (i in penguins){
			penguins[i].dir = turn_dirs[i];
		}
	}
}

inline stun_only_cleanup() {
	int z;
	for (z in penguins){
		if
		:: penguins[z].health <= 0 ->
			penguins[z].stunned = true;
		:: else
		fi;
	}
}

inline big_cleanup() {
	d_step {
		int z;
		for (z in penguins){
			if
			:: penguins[z].health <= 0 && penguins[z].curr_pos.x != OFF_BOARD ->
				penguins[z].stunned = true;
				penguins[z].curr_pos.x = OFF_BOARD;
				penguins[z].curr_pos.y = OFF_BOARD;
				penguins[z].has_snowball = false;
			:: penguins[z].stunned && penguins[z].curr_pos.x == OFF_BOARD ->
				relocate(penguins[z].curr_pos, penguins[z].home);
				penguins[z].has_snowball = true;
				penguins[z].health = 3;
				penguins[z].stunned = false;
			:: else -> //not stunned, on board
				penguins[z].has_snowball = true;
			fi;
		}
	}
}

inline check_victory() {
	d_step {
		int p;
		int max_points = 0;
		int max_count = 0;
		for (p in penguins){
			if
			:: penguins[p].points > max_points ->
				max_count = 1;
				max_points = penguins[p].points;
			:: penguins[p].points == max_points ->
				max_count++;
			:: else
			fi;
		}
		if
		:: max_points >= 5 && max_count == 1 ->
			game_over = true;
		:: max_points > INFINITY ->
			assert(false)
		:: else
		fi;
	}
}

inline setup(p){
	penguins[p].stunned = false;
	penguins[p].health = 3;
	penguins[p].has_snowball = true;
	penguins[p].points = 0;
	penguins[p].dir = p;
    int i;
	for (i : 0 .. NUM_CARDS - 1){
		penguins[p].has_card[i] = true;
		penguins[p].using_card[i] = false;
        penguins[p].has_used_card[i] = false;
	}
	if
	:: p == NORTH ->
		penguins[p].home.x = CENTER;
		penguins[p].home.y = BOARD_SIZE - 1;
	:: p == SOUTH ->
		penguins[p].home.x = CENTER;
		penguins[p].home.y = 0;
	:: p == EAST ->
		penguins[p].home.x = BOARD_SIZE - 1;
		penguins[p].home.y = CENTER;
	:: p == WEST ->
		penguins[p].home.x = 0;
		penguins[p].home.y = CENTER;
	fi;
	relocate(penguins[p].curr_pos, penguins[p].home);
}

inline relocate(old_pos, new_pos){
	old_pos.x = new_pos.x;
	old_pos.y = new_pos.y;
}

inline pick_cards(){
	int p;
	for (p in penguins) {
		int card;
		select (card : 0 .. NUM_CARDS);
		if 
		:: card < NUM_CARDS && penguins[p].has_card[card]->
			penguins[p].has_card[card] = false;
			penguins[p].using_card[card] = true;
		:: else
		fi;
	}
}

inline use_earmuffs() {
	int p;
	for (p in penguins) {
		if
		:: penguins[p].using_card[EARMUFFS] ->
			penguins[p].health++;
			penguins[p].using_card[EARMUFFS] = false;
            penguins[p].has_used_card[EARMUFFS] = true;
		:: else
		fi;
	}
}

active proctype game () {
	//Instantiate penguins.
	d_step {
		int penguin;
		for (penguin in penguins){
			setup(penguin);
		}
	}
	do
	:: game_over ->
		break;
	:: else ->
		atomic {
			ltl_okay = false;
			pick_cards();
			use_earmuffs();
			move();
			shoot();
			big_cleanup();
			turn();
			check_victory();
			ltl_okay = true;
	   }
	od;
}

//LTL Assertions
//Points strictly increase.
//Always possible to reach a winning state.

int never__p;
bool never__in_bounds;
never {
	do
	:: ltl_okay -> 
		//Penguins are on board XOR stunned.
		for (never__p in penguins){
			check_in_bounds(penguins[never__p].curr_pos, never__in_bounds);
			if
			:: penguins[never__p].stunned && never__in_bounds ->
				goto violation;
			:: (penguins[never__p].curr_pos.x == OFF_BOARD && 
				penguins[never__p].curr_pos.y == OFF_BOARD) && 
			   !penguins[never__p].stunned ->
				goto violation;
			:: else
			fi;
		}
		//Stunned penguin never has positive health.
		for (never__p in penguins){
			if
			:: penguins[never__p].stunned && penguins[never__p].health > 0 ->
				goto violation;
			:: else
			fi;
		}
	:: else
	od;
	violation: skip
}

//We can show that it is possible to have infinite gameplay.
ltl game_can_end { always (eventually game_over)}
//Every penguin either has one of each card or has used that card.
ltl no_card_reuse { always (ltl_okay implies
    ((penguins[0].has_card[0] == !penguins[0].has_used_card[0]) &&
    (penguins[0].has_card[1] == !penguins[0].has_used_card[1]) &&
    (penguins[0].has_card[2] == !penguins[0].has_used_card[2]) &&
    (penguins[1].has_card[0] == !penguins[1].has_used_card[0]) &&
    (penguins[1].has_card[1] == !penguins[1].has_used_card[1]) &&
    (penguins[1].has_card[2] == !penguins[1].has_used_card[2]) &&
    (penguins[2].has_card[0] == !penguins[2].has_used_card[0]) &&
    (penguins[2].has_card[1] == !penguins[2].has_used_card[1]) &&
    (penguins[2].has_card[2] == !penguins[2].has_used_card[2]) &&
    (penguins[3].has_card[0] == !penguins[3].has_used_card[0]) &&
    (penguins[3].has_card[1] == !penguins[3].has_used_card[1]) &&
    (penguins[3].has_card[2] == !penguins[3].has_used_card[2])))}
