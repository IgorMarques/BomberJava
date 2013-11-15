package graphics.window;

import game_objects.Map;
import game_objects.Player;
import graphics.core.GameGraphics;
import graphics.input.GameKeyListener;
import graphics.objects.Drawable;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.image.BufferStrategy;

import javax.swing.JFrame;

import constants.Constants.Movement;

import core.Game;

public class GameWindow extends JFrame implements Drawable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 5593300460625998050L;
	
	private Graphics g;
	private BufferStrategy bStrategy;
	private GameGraphics game;
	
	private boolean gameRunning = true;

	private long lastFpsTime;

	private int fps;
	
	public GameWindow(final GameGraphics game) {
		super("Bomber Java");
		
		this.game = game;
		
		setPreferredSize(new Dimension(500, 500));
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		pack();
		setVisible(true);
		
		KeyListener keyListener = new GameKeyListener();
		
		addKeyListener(keyListener);
		
		createBufferStrategy(2);
		bStrategy = this.getBufferStrategy();
	}

	
	public void gameLoop() {
		long lastLoopTime = System.nanoTime();
		final int TARGET_FPS = 28;
		final long OPTIMAL_TIME = 1000000000 / TARGET_FPS;

		// keep looping round til the game ends
		while (gameRunning) {
			// work out how long its been since the last update, this
			// will be used to calculate how far the entities should
			// move this loop
			long now = System.nanoTime();
			long updateLength = now - lastLoopTime;
			lastLoopTime = now;
			double delta = updateLength / ((double) OPTIMAL_TIME);

			// update the frame counter
			lastFpsTime += updateLength;
			fps++;

			// update our FPS counter if a second has passed since
			// we last recorded
			if (lastFpsTime >= 1000000000) {
				System.out.println("(FPS: " + fps + ")");
				lastFpsTime = 0;
				fps = 0;
			}

			// update the game logic
			doGameUpdates(delta);

			//draw on memory
			draw(bStrategy.getDrawGraphics());
			
			// draw everyting
			render();

			// we want each frame to take 10 milliseconds, to do this
			// we've recorded when we started the frame. We add 10 milliseconds
			// to this and then factor in the current time to give
			// us our final value to wait for
			// remember this is in ms, whereas our lastLoopTime etc. vars are in
			// ns.
			long sleep = (lastLoopTime - System.nanoTime() + OPTIMAL_TIME) / 1000000;
			try {
				if (sleep > 0)
					Thread.sleep(sleep);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}

	private void render() {
		bStrategy.show();
	}

	private void doGameUpdates(double delta) {
		
	}

	@Override
	public void draw(Graphics g) {
		Graphics2D g2d = (Graphics2D) g;
		g2d.clearRect(0, 0, 500, 500);
		
		game.draw(g2d);
	}
	
	public static void main(String[] args) {
		Game game = new Game(new Map());
		
		GameWindow window = new GameWindow(new GameGraphics(game));
		window.gameLoop();
	}
}
