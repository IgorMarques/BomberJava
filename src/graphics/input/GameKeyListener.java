package graphics.input;

import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.util.HashMap;

public class GameKeyListener implements KeyListener {

	private HashMap<Integer, Boolean> keys;
	
	public GameKeyListener() {
		keys = new HashMap<Integer, Boolean>();
		keys.put(KeyEvent.VK_LEFT, false);
		keys.put(KeyEvent.VK_RIGHT, false);
		keys.put(KeyEvent.VK_UP, false);
		keys.put(KeyEvent.VK_DOWN, false);
		keys.put(KeyEvent.VK_SPACE, false);
		keys.put(KeyEvent.VK_ESCAPE, false);
		keys.put(KeyEvent.VK_SHIFT, false);
	}
	
	public void keyPressed(KeyEvent e) {
		if (e.getKeyCode() == KeyEvent.VK_ESCAPE)
			System.exit(0);
		
		keys.put(e.getKeyCode(), true);
	}

	public void keyReleased(KeyEvent e) {
		keys.put(e.getKeyCode(), false);
	}

	public void keyTyped(KeyEvent e) {
	}
	
	public boolean isPressed(int key) {
		return keys.get(key);
	}
}
