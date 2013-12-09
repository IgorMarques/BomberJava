package game_objects;

import core.Game;
import events.ExplodeEvent;
import behavior.Explodable;

public class Block extends GameObject implements Explodable {
	
	private /*@ spec_public @*/ boolean explodable = true;
	//@ public initially explodable == true;
	
	//@ public invariant explodable == true;
	
	//usar heranca aqui
	public Block(Game game, int x, int y) {
		super(game, x, y);
	}
	
	/*@ requires true;
	@ assignable getGame();
	@ ensures (
	@ \forall int i; 0 <=i && i  <getGame().getObjects().length;
	@			getGame().getObjects()[i] != this;
	@) 
	@ public constraint
	@	ensures \old(getGame().getObjects().length)-1 == getGame().getObjects.length
	@*/
	public void exploded(ExplodeEvent e) {
		getGame().removeObject(this);
	}

	
	/*@ requires true;
	 @ assignable \nothing;
	 @ ensures \return == this.explodable;@*/
	public /*@pure@*/ boolean isExplodable() {
		return explodable;
	}

	/*@ requires true;
	 @ assignable explodable;
	 @ ensures this.explodable == explodable;@*/
	public void setExplodable(boolean explodable) {
		this.explodable = explodable;
	}

	public void update(double delta) {
	}

}
