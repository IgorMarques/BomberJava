package game_objects;

import core.Game;

public abstract class PowerUp extends GameObject {
	public PowerUp(Game game, int x, int y) {
		super(game, x, y);
	}

	/*@ requires true
	@*/
	public abstract void execute(Player player);
}
