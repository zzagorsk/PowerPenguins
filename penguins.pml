#define NORTH 1
#define EAST 2
#define SOUTH 3
#define WEST 4

#define BOARD_SIZE 7
#define MAX_MOVE 5
#define NUM_PENGUINS 4

typedef Point {
	int x;
	int y;
}

typedef Penguin {
	Point currPos;
	int dir;
	int health;
	int points;
	Point home;
	bool stunned;
}

Penguin penguins[NUM_PENGUINS];

inline move() {
	int i;
	for (i in penguins) {
		int max_dist;
		max_move_dist(penguins[i], max_dist);
		int dist;
		select (dist : 0 .. max_dist);
		move_penguin(penguins[i], dist)
	}
	//check_collisions();
}

inline max_move_dist(p, dist) {
	if
	:: p.dir == NORTH ->
		max(p.currPos.y, MAX_MOVE, dist);
	:: p.dir == EAST  ->
		max((BOARD_SIZE - p.currPos.x), MAX_MOVE, dist);
	:: p.dir == SOUTH ->
		max((BOARD_SIZE - p.currPos.y), MAX_MOVE, dist);
	:: p.dir == WEST  ->
		max(p.currPos.x, MAX_MOVE, dist);
	fi;
}

inline move_penguin(p, dist) {
	if
	:: p.dir == NORTH -> 
		p.currPos.y = p.currPos.y - dist;
	:: p.dir == EAST  -> 
		p.currPos.x = p.currPos.x + dist;
	:: p.dir == SOUTH -> 
		p.currPos.y = p.currPos.y + dist;
	:: p.dir == WEST  -> 
		p.currPos.x = p.currPos.x - dist;
	fi;	
}
	
inline max(a, b, bigger) {
	if 
	:: a > b -> bigger = a;
	:: else  -> bigger = b;
	fi;
}

/*
inline check_collisions() {
	//perform collision checks
}
*/

inline shoot() {
	int i;
	for (i in penguins){
		int shoot_dir;
		select (shoot_dir : 1 .. 4);
		//check for penguins in targeted squares
		//deal damage.
		//gain points.
	}
}

inline turn() {
	int i;
	for (i in penguins){
		int turn_dir;
		select (turn_dir : 1 .. 4);
		penguins[i].dir = turn_dir;
	}
}

active proctype game () {
	//Instantiate penguins.

	do
	:: move();
	   shoot();
	   //cleanup();
	   turn();
	od;
}

//LTL Assertions
//Penguins are on board.
//Points strictly increase.
//Stunned penguin implies 0 health.
//Always possible to reach a winning state.
